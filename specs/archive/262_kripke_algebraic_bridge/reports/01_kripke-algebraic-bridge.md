# Research Report: Kripke-Algebraic Bridge for Intuitionistic Propositional Logic

**Task**: 262 -- Implement Kripke-algebraic bridge  
**Session**: sess_1782145977_f2ba80  
**Date**: 2026-06-22

## 1. Executive Summary

The task is to prove that upward-closed sets of a Kripke frame's preorder form a Heyting
algebra, and connect `IForces` to `AlgEvaluate` via this construction. Research confirms
this is entirely feasible using existing Mathlib infrastructure and CSLib definitions. The
key insight is that `LowerSet (OrderDual World)` in Mathlib provides exactly the Heyting
algebra of upward-closed sets with the subset ordering, and its Heyting implication matches
the Kripke forcing clause for implication. No new axioms or sorry-deferral patterns are needed.

## 2. Existing CSLib Infrastructure

### 2.1 Kripke Semantics (`Cslib/Logics/Propositional/Semantics/Kripke.lean`)

- **`IForces`**: Forcing relation for propositional Kripke semantics. Takes `v : World -> Atom -> Prop`,
  `bot_forces : World -> Prop`, and a world `w`. Five cases: atom (valuation lookup), bot
  (`bot_forces`), imp (universal quantification over successors), and/or.
- **`iforces_persistence`**: Upward-closure of forcing under the preorder.
- **`IValid`**: Intuitionistic validity (bot_forces = fun _ => False).
- **`MValid`**: Minimal validity (arbitrary upward-closed bot_forces).
- **`KripkeModel`**: Structure bundling preordered worlds, valuation, bot_forces, and
  upward-closure proofs.

### 2.2 Algebraic Semantics (`Cslib/Logics/Propositional/Semantics/Algebra.lean`)

- **`AlgEvaluate`**: Generic evaluator mapping propositions to elements of a
  `GeneralizedHeytingAlgebra H`. Takes `v : Atom -> H` and explicit `bot_val : H`.
  Connectives map to: `atom x -> v x`, `bot -> bot_val`, `imp -> himp`, `and -> inf`, `or -> sup`.
- **`GHAValid`**, **`HAValid`**, **`BAValid`**: Validity at each algebra tier.
- **`AlgTValid`**: Theory validity (all axioms evaluate to top).

### 2.3 Existing Bridge (`Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean`)

The existing Bridge.lean connects `AlgEvaluate` to:
- `Evaluate` (Prop-valued bivalent evaluator) via `propEvaluateEq`
- `BoolEvaluate` (Bool-valued evaluator) via `boolEvaluateEq`

**No bridge between `IForces` and `AlgEvaluate` exists yet.** This is the gap task 262 fills.

### 2.4 Algebraic Completeness (`Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean`)

- **`Theory.alg_complete`**: General algebraic completeness via Lindenbaum algebra.
- **`IPL.alg_complete`**: IPL completeness w.r.t. HeytingAlgebra.
- **`LindenbaumAlgebra`**: Quotient of propositions by T-equivalence, with `GeneralizedHeytingAlgebra`
  and `HeytingAlgebra` instances.

### 2.5 Kripke Completeness (`Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean`)

- **`int_strong_completeness`**: Strong completeness for IPL via canonical model (prime DCCS worlds).
- **`int_soundness_completeness`**: `IValid phi <-> Derivable IntPropAxiom phi`.

### 2.6 Proposition Type (`Cslib/Logics/Propositional/Defs.lean`)

`PL.Proposition Atom` has five constructors: `atom | bot | imp | and | or`. Negation, verum,
and biconditional are derived connectives. The type is in namespace `Cslib.Logic.PL`.

## 3. Mathlib Infrastructure

### 3.1 UpperSet and LowerSet

Mathlib's `UpperSet alpha` (bundled upward-closed sets) uses a **reversed** ordering:
- `U <= V` iff `V.carrier ⊆ U.carrier`
- `U ⊓ V` has carrier `U.carrier ∪ V.carrier`
- `U ⊔ V` has carrier `U.carrier ∩ V.carrier`
- `⊥ = Set.univ`, `⊤ = ∅`

This is the **opposite** of what we need for the bridge.

### 3.2 Key Discovery: `LowerSet (OrderDual World)`

`LowerSet (OrderDual World)` provides exactly the right algebra:
- A lower set in `(OrderDual World)` is a set S such that if `a ∈ S` and `b ≤_dual a`
  (i.e., `a ≤ b` in World) then `b ∈ S` -- this is an upward-closed set in World.
- The ordering is natural subset inclusion: `U ≤ V iff U ⊆ V`.
- `⊓` is set intersection (matching `and`).
- `⊔` is set union (matching `or`).
- `⊥ = ∅` (matching `bot_forces = fun _ => False`).
- `⊤ = Set.univ`.

### 3.3 Heyting Algebra Instance

```
HeytingAlgebra (LowerSet (OrderDual World))
```

This instance exists in Mathlib, derived via:
`LowerSet -> CompleteLattice -> CompletelyDistribLattice -> Order.Frame -> HeytingAlgebra`

### 3.4 Heyting Implication Characterization

The Frame-derived `himp` for `LowerSet alpha` satisfies:

```
x ∈ (U ⇨ V : LowerSet alpha) ↔ ∀ y, y ≤ x → y ∈ U → y ∈ V
```

Instantiated at `alpha = OrderDual World`:

```
toDual w ∈ (U ⇨ V : LowerSet (OrderDual World)) ↔ 
  ∀ w', w ≤ w' → toDual w' ∈ U → toDual w' ∈ V
```

**This is exactly the Kripke forcing clause for implication.** This was verified in Lean
using `le_himp_iff` (the adjunction characterization) and `lowerClosure` for principal
lower sets.

### 3.5 Key Mathlib Lemmas

| Lemma | Type | Purpose |
|-------|------|---------|
| `le_himp_iff` | `W ≤ U ⇨ V ↔ W ⊓ U ≤ V` | Adjunction for himp |
| `LowerSet.coe_inf` | `↑(s ⊓ t) = ↑s ∩ ↑t` | Meet = intersection |
| `LowerSet.coe_sup` | `↑(s ⊔ t) = ↑s ∪ ↑t` | Join = union |
| `LowerSet.coe_bot` | `↑⊥ = ∅` | Bottom = empty |
| `LowerSet.coe_top` | `↑⊤ = Set.univ` | Top = whole set |
| `lowerClosure` | `Set α → LowerSet α` | Principal lower set construction |
| `subset_lowerClosure` | `s ⊆ ↑(lowerClosure s)` | Element is in its closure |
| `OrderDual.toDual` / `ofDual` | `α ↔ αᵒᵈ` | Dual order coercion |

## 4. Bridge Construction Plan

### 4.1 Type Alias

Define `UpsetAlgebra World := LowerSet (OrderDual World)` as a convenient alias for the
Heyting algebra of upward-closed sets.

### 4.2 Constructor: `mkUpset`

Build an element of `UpsetAlgebra World` from an upward-closed predicate:

```lean
def mkUpset (P : World → Prop) (hP : ∀ {w w'}, w ≤ w' → P w → P w') :
    UpsetAlgebra World
```

Carrier is `{x : OrderDual World | P (OrderDual.ofDual x)}`. The `lower'` proof follows
from `hP` via the order reversal.

### 4.3 Upset Valuation

Define the valuation mapping atoms to their truth sets:

```lean
def upsetVal (v : World → Atom → Prop)
    (v_uc : ∀ {w w'} (p : Atom), w ≤ w' → v w p → v w' p) :
    Atom → UpsetAlgebra World :=
  fun p => mkUpset (fun w => v w p) (v_uc p)
```

### 4.4 Upset Bot Value

Define the bottom value from bot_forces:

```lean
def upsetBotVal (bf : World → Prop)
    (bf_uc : ∀ {w w'}, w ≤ w' → bf w → bf w') :
    UpsetAlgebra World :=
  mkUpset bf bf_uc
```

For intuitionistic semantics: `upsetBotVal (fun _ => False) (fun _ h => h) = ⊥`.

### 4.5 Main Bridge Theorem

The central result, proved by structural induction on formulas:

```lean
theorem kripkeAlgBridge (v : World → Atom → Prop) (bf : World → Prop)
    (v_uc : ∀ {w w'} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w'}, w ≤ w' → bf w → bf w')
    (w : World) (φ : PL.Proposition Atom) :
    IForces v bf w φ ↔
      OrderDual.toDual w ∈ AlgEvaluate (upsetVal v v_uc) (upsetBotVal bf bf_uc) φ
```

**Proof sketch by induction on φ:**
- **atom p**: Both sides reduce to `v w p`. Immediate.
- **bot**: Both sides reduce to `bf w`. Immediate.
- **and φ ψ**: IForces gives `∧`; AlgEvaluate gives `⊓` on UpsetAlgebra. By IH and
  `LowerSet.coe_inf` (inf = intersection), both sides are `IForces φ ∧ IForces ψ`.
- **or φ ψ**: Analogous, using `LowerSet.coe_sup` (sup = union).
- **imp φ ψ**: IForces gives `∀ w' ≥ w, IForces φ w' → IForces ψ w'`. AlgEvaluate gives
  `toDual w ∈ (eval φ ⇨ eval ψ)`. By IH and `upset_himp_char`, both sides are equivalent
  to `∀ w', w ≤ w' → toDual w' ∈ eval φ → toDual w' ∈ eval ψ`.

### 4.6 Corollaries

**IValid iff HAValid via upsets:**
```lean
theorem ivalid_iff_havalid (φ : PL.Proposition Atom) :
    IValid φ ↔ HAValid φ
```

Proof direction `IValid → HAValid` can use `int_soundness_completeness` plus
`int_alg_soundness_derivable`. Direction `HAValid → IValid` uses the bridge: HAValid means
`AlgEvaluate v ⊥ φ = ⊤` for every HA including `UpsetAlgebra World`, which via the bridge
gives `IForces v (fun _ => False) w φ` for all w, i.e., `IValid`.

**MValid iff GHAValid via upsets:**
```lean
theorem mvalid_iff_ghavalid (φ : PL.Proposition Atom) :
    MValid φ ↔ GHAValid φ
```

Analogous using `upsetBotVal` with arbitrary `bot_val`.

### 4.7 Alternative: Direct Equivalence Without Detour Through Derivability

The bridge gives a **semantic** path between Kripke and algebraic validity, without routing
through the proof system. This is the key added value over what exists: the current path is
`IValid ↔ Derivable ↔ HAValid` (through completeness). The bridge provides `IValid ↔ HAValid`
directly, which is conceptually cleaner and avoids `DecidableEq Atom` requirements that the
completeness theorems carry.

## 5. File Organization Recommendation

Create a single new file:

```
Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean
```

This follows the pattern of the existing `Bridge.lean` (which connects Evaluate/BoolEvaluate
to AlgEvaluate) by adding a parallel bridge for IForces/MForces.

**Imports needed:**
- `Cslib.Logics.Propositional.Semantics.Kripke` (for IForces, IValid, MValid)
- `Cslib.Logics.Propositional.Semantics.Algebra` (for AlgEvaluate, HAValid, GHAValid)
- `Mathlib.Order.UpperLower.CompleteLattice` (for LowerSet, CompleteLattice)
- `Mathlib.Order.UpperLower.Closure` (for lowerClosure)
- `Mathlib.Order.Heyting.Basic` (for HeytingAlgebra, le_himp_iff)

**Estimated size**: 200-300 lines (definitions + bridge theorem + corollaries + docstrings).

## 6. Risk Assessment

### Low Risk
- **Mathlib API stability**: All required APIs (`LowerSet`, `le_himp_iff`, `HeytingAlgebra`)
  are well-established in Mathlib. No experimental or unstable features are used.
- **Proof complexity**: The bridge theorem is a structural induction with five cases, each
  following directly from the HA operations matching the IForces clauses. The imp case is the
  most involved but the `upset_himp_char` lemma (verified in Lean) handles it cleanly.

### Moderate Consideration
- **OrderDual ceremony**: Working with `OrderDual.toDual`/`ofDual` coercions adds some
  syntactic overhead. The `mkUpset` constructor abstracts this cleanly.
- **`upsetBotVal (fun _ => False) = ⊥` proof**: Need to show the mkUpset of `False` equals
  `⊥` in `LowerSet (OrderDual World)`. Should follow from `LowerSet.coe_bot` = `∅` and
  extensionality.

### No Blockers
- All necessary Mathlib instances exist and were verified.
- The main theorem was prototyped (himp characterization) and compiles.
- No sorry deferral needed for any step.

## 7. Tactic Survey

For the bridge theorem proof:
- **simp**: Useful for unfolding `AlgEvaluate_*` lemmas and `IForces_*` lemmas.
- **ext**: For showing equality of `LowerSet` elements (two sets with same members are equal).
- **constructor/cases**: For iff proofs and handling the ∧/∨ cases.
- **le_himp_iff**: The key algebraic tool for the imp case.
- **induction**: Structural induction on `PL.Proposition` for the main theorem.

## 8. Reuse Check Results

| Concept | CSLib Status | Mathlib Status |
|---------|-------------|---------------|
| Upward-closed sets as HA | NOT in CSLib | `LowerSet (OrderDual α)` has HeytingAlgebra ✓ |
| IForces | In CSLib (`Kripke.lean`) ✓ | N/A |
| AlgEvaluate | In CSLib (`Algebra.lean`) ✓ | N/A |
| le_himp_iff | N/A | In Mathlib ✓ |
| lowerClosure | N/A | In Mathlib ✓ |
| Bridge (IForces ↔ AlgEvaluate) | NOT in CSLib (gap) | N/A |

**No new foundational abstractions needed.** The bridge uses existing CSLib definitions
and Mathlib's HA infrastructure without introducing new typeclasses or structures.
