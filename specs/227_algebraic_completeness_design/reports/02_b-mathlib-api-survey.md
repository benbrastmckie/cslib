# Mathlib API Survey for Algebraic Completeness Infrastructure

**Task**: 227 -- Algebraic completeness design
**Teammate**: B -- Mathlib API availability and gaps
**Session**: sess_1750130000_research227

## Executive Summary

Mathlib provides a strong foundation for algebraic completeness proofs: complete `HeytingAlgebra`
hierarchy, bundled `HeytingHom`, `BooleanAlgebra.ofRegular`, `LatticeCon`, and mature `Finset.inf`
API. The major gap is the Dedekind-MacNeille completion, which does not exist in Mathlib. xcthulhu
provides a custom implementation in `Cslib/ForMathlib/Order/`. No `JohanssonAlgebra` type exists
in Mathlib -- this is a new abstraction CSLib must define for the minimal logic tier (MPL).

---

## 1. Dedekind-MacNeille Completion

### Status: NOT IN MATHLIB -- Custom Build Required

**Searches performed**:
- `lean_local_search "DedekindMacNeille"` -- 0 results
- `lean_local_search "MacNeille"` -- 0 results
- `lean_loogle "DedekindMacNeille"` -- 0 results
- `lean_leanfinder "Dedekind-MacNeille completion"` -- returned only `CompleteSublattice`
  and `Function.Injective.completeLattice` (general lattice pullback, not D-M specific)

**Conclusion**: Mathlib has no Dedekind-MacNeille completion whatsoever.

### xcthulhu's Implementation

Located at: `Cslib/ForMathlib/Order/` in the xcthulhu/cslib fork (ref `488309e3`).

**File**: `Cslib/Logics/Propositional/Semantics/DedekindMacneille.lean`
- Author: Yijun Yuan
- Namespace: `OrderTheory`
- Approach: Uses `ClosureOperator.Closeds` over a Galois connection between upper/lower bounds

**Key definitions**:
- `DedekindMacNeilleClosureOperator α` -- closure operator via `GaloisConnection.closureOperator`
- `DedekindMacNeilleCompletion α` -- `abbrev` for `(DedekindMacNeilleClosureOperator α).Closeds`
- `coe' : α ↪o DedekindMacNeilleCompletion α` -- order embedding via principal down-sets `Set.Iic x`
- Custom `CompleteLattice` instance on `ClosureOperator.Closeds T` (general, for any closure op)
- `HeytingAlgebra (DedekindMacNeilleCompletion α)` instance when `α` has `GeneralizedHeytingAlgebra`
- `LinearOrder` and `CompleteLinearOrder` when `α` has `LinearOrder`
- Universal property: `univ_prop_DedekindMacNeilleCompletion` for extending order embeddings

**Heyting algebra structure on completion**: The key instance defines `himp` on closed sets:
```
A ⇨ B := {x | forall y in A.val, x ⊓ y in B.val}
```
This is proved to satisfy `le_himp_iff`. The completion is a full `HeytingAlgebra` (not just
`GeneralizedHeytingAlgebra`) -- it gains `⊥` from the closure of the empty set.

**Critical simp lemmas provided**:
- `DedekindMacNeilleCompletion.coe_inf`: `↑(x ⊓ y) = ↑x ⊓ ↑y`
- `DedekindMacNeilleCompletion.coe_sup`: `↑(x ⊔ y) = ↑x ⊔ ↑y`
- `DedekindMacNeilleCompletion.coe_himp`: `↑(x ⇨ y) = ↑x ⇨ ↑y`

These are essential for the completeness proof: the canonical valuation maps atoms to the
Lindenbaum quotient and the `coe_himp` lemma lets the completion preserve the algebraic structure.

### Gap Assessment

The D-M completion code is xcthulhu-only. To use it in CSLib:
1. The `ClosureOperator.Closeds` CompleteLattice instance should be proposed for Mathlib
2. The D-M-specific code can live in `Cslib/ForMathlib/Order/`
3. Universe polymorphism: the current code is universe-polymorphic (good)
4. The `coe'` embedding is an `OrderEmbedding`, sufficient for the completeness argument

**Estimate**: ~500 lines of infrastructure, already written by xcthulhu/Yuan. Needs review and
adaptation to CSLib's current Lean toolchain version.

---

## 2. Heyting Algebra Homomorphisms

### Status: FULLY IN MATHLIB

**File**: `Mathlib/Order/Heyting/Hom.lean` (Yaeel Dillies)

**Available types**:
| Type | Preserves | Extends |
|------|-----------|---------|
| `HeytingHom α β` | `⊥`, `⇨`, `⊓`, `⊔` | `LatticeHom` |
| `CoheytingHom α β` | `⊤`, `\`, `⊓`, `⊔` | `LatticeHom` |
| `BiheytingHom α β` | `⇨`, `\`, `⊓`, `⊔` | `LatticeHom` |
| `HeytingHomClass F α β` | Typeclass for `HeytingHom`-like types | `LatticeHomClass` |

**Key API**:
- `HeytingHom.id`, `HeytingHom.comp` -- identity and composition
- `HeytingHomClass.toBoundedLatticeHomClass` -- automatic `⊤` preservation (from `⊥ ⇨ ⊥ = ⊤`)
- `map_compl`, `map_himp` -- simp lemmas
- `OrderIsoClass.toHeytingHomClass` -- order isos automatically preserve Heyting implication
- `BoundedLatticeHomClass.toBiheytingHomClass` -- for `BooleanAlgebra`, bounded lattice hom suffices

**What's NOT in Mathlib but xcthulhu provides**:

File: `Cslib/ForMathlib/Order/Heyting/Hom.lean` (Thomas Waring)

- `HImpHom α β` -- homomorphism preserving only `⇨` (no lattice structure required)
- `HImpHomClass F α β` -- typeclass
- `GeneralizedHeytingHom α β` -- `LatticeHom` + `HImpHom` for `GeneralizedHeytingAlgebra`
- `GeneralizedHeytingHomClass F α β` -- typeclass

These are needed because the Lindenbaum quotient map for the canonical valuation sends
propositions homomorphically through a `GeneralizedHeytingAlgebra` (not full `HeytingAlgebra`),
and Mathlib's `HeytingHom` requires the full `HeytingAlgebra` constraint.

**Recommendation**: Use `GeneralizedHeytingHom` from xcthulhu's ForMathlib for the MPL tier.
The existing Mathlib `HeytingHom` suffices for IPL and CPL tiers.

---

## 3. Quotient Lattice / Algebra Constructions

### LatticeCon: IN MATHLIB (new, 2025)

**File**: `Mathlib/Order/Lattice/Congruence.lean` (Christopher Hoskin, 2025)

**Structure**: `LatticeCon α` extends `Setoid α` with:
```lean
inf : forall {w x y z}, r w x -> r y z -> r (w ⊓ y) (x ⊓ z)
sup : forall {w x y z}, r w x -> r y z -> r (w ⊔ y) (x ⊔ z)
```

**API**:
- `LatticeCon.mk'` -- alternative construction from 4 conditions
- `LatticeCon.ker` -- kernel of a `LatticeHom` as a `LatticeCon`

**What's missing**: There is no `HeytingCon` or quotient Heyting algebra construction. The
`LatticeCon` gives you a quotient lattice but not a quotient with `⇨` preservation. Also no
direct `LatticeCon.Quotient` type -- only the abstract congruence data.

### Con (for groups/monoids): IN MATHLIB

**File**: `Mathlib/GroupTheory/Congruence/Defs.lean`

- `Con M` for `[Mul M]` -- congruence on a multiplicative type
- `Con.Quotient` -- quotient by congruence
- `Con.instCompleteLattice` -- congruences form a complete lattice

This is for algebraic (group/ring) quotients, not lattice quotients. Not directly applicable.

### xcthulhu's Lindenbaum Quotient Approach

xcthulhu does NOT use `LatticeCon`. Instead, he builds the quotient directly:

1. Define `propositionSetoid` from provable equivalence
2. Use `Quotient.lift₂` to lift lattice operations
3. Manually construct `PartialOrder`, `Lattice`, `GeneralizedHeytingAlgebra`, `HeytingAlgebra`,
   `BooleanAlgebra` instances on the quotient

This is more work but gives full control. The key insight: provable equivalence is a congruence
for all propositional connectives, so each operation lifts cleanly.

### BimodalLogic's Approach

The BimodalLogic project uses a similar manual quotient construction:
- `provEquivSetoid` from `ProvEquiv` (provable biconditional)
- `Quotient.lift` for each operation (neg, imp, and, or, box, G, H)
- Temporal duality (`sigma_quot`) also lifted to the quotient
- Currently has `sorry` in `provEquiv_all_future_congr` (needs temp_k_dist from BX axioms)

### Recommendation for Task 227

For the Lindenbaum quotient, follow xcthulhu's approach: manual quotient with `Quotient.lift₂`.
`LatticeCon` could theoretically be used but would require extending it to handle `⇨` preservation,
which is more work than the manual approach. The xcthulhu code already demonstrates the full
construction from `PartialOrder` through `BooleanAlgebra`.

---

## 4. GeneralizedHeytingAlgebra API Survey

### Hierarchy

```
GeneralizedHeytingAlgebra α
  extends Lattice α, OrderTop α, HImp α
  field: le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c

HeytingAlgebra α
  extends GeneralizedHeytingAlgebra α, OrderBot α, Compl α
  field: himp_bot : a ⇨ ⊥ = aᶜ

BooleanAlgebra α
  (in Mathlib/Order/BooleanAlgebra/Defs.lean)
  extends HeytingAlgebra α (via GeneralizedHeytingAlgebra.toDistribLattice)
```

### Key simp Lemmas for `⇨` (himp)

All in `Mathlib/Order/Heyting/Basic.lean`:

| Lemma | Statement | Tier |
|-------|-----------|------|
| `le_himp_iff` | `a ≤ b ⇨ c ↔ a ⊓ b ≤ c` | GHA (Galois adjunction) |
| `himp_eq_top_iff` | `a ⇨ b = ⊤ ↔ a ≤ b` | GHA |
| `himp_self` | `a ⇨ a = ⊤` | GHA |
| `himp_inf_le` | `(a ⇨ b) ⊓ a ≤ b` | GHA (modus ponens) |
| `inf_himp_le` | `a ⊓ (a ⇨ b) ≤ b` | GHA |
| `himp_himp` | `a ⇨ b ⇨ c = a ⊓ b ⇨ c` | GHA (currying) |
| `himp_left_comm` | `a ⇨ b ⇨ c = b ⇨ a ⇨ c` | GHA |
| `himp_inf_distrib` | `a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c)` | GHA |
| `sup_himp_distrib` | `a ⊔ b ⇨ c = (a ⇨ c) ⊓ (b ⇨ c)` | GHA |
| `himp_le_himp` | `a ≤ b → c ≤ d → b ⇨ c ≤ a ⇨ d` | GHA (monotonicity) |
| `inf_himp` | `a ⊓ (a ⇨ b) = a ⊓ b` | GHA |
| `top_himp` | `⊤ ⇨ a = a` | GHA |
| `himp_top` | `a ⇨ ⊤ = ⊤` | GHA |
| `himp_bot` | `a ⇨ ⊥ = aᶜ` | HA |
| `bot_himp` | `⊥ ⇨ a = ⊤` | HA (ex falso) |
| `compl_compl` | `aᶜᶜ = a` | BA |
| `himp_eq` | `a ⇨ b = b ⊔ aᶜ` | BA |

### Mapping to Axiom Tiers

**MPL (GHA-level soundness)**:
- `implyK`: `le_himp_iff` + `inf_le_left`
- `implyS`: `himp_inf_le` (used 3 times)
- `andI/andE1/andE2`: `le_inf`, `inf_le_left`, `inf_le_right`
- `orI1/orI2/orE`: `le_sup_left`, `le_sup_right`, `inf_sup_left`

**IPL (HA-level soundness)**:
- All MPL lemmas + `bot_le` (for ex falso quodlibet)

**CPL (BA-level soundness)**:
- All IPL lemmas + `himp_eq`, `compl_compl` (for Peirce's law)

CSLib's existing `Algebra/Soundness.lean` already uses exactly these lemmas and the proofs
compile. This API is mature and stable.

### Important HA-specific Lemmas

| Lemma | Statement |
|-------|-----------|
| `compl_top` | `(⊤ : α)ᶜ = ⊥` |
| `compl_bot` | `(⊥ : α)ᶜ = ⊤` |
| `le_compl_compl` | `a ≤ aᶜᶜ` |
| `compl_le_compl` | `a ≤ b → bᶜ ≤ aᶜ` |
| `compl_compl_compl` | `aᶜᶜᶜ = aᶜ` |
| `compl_compl_inf_distrib` | `(a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ` |
| `compl_compl_himp_distrib` | `(a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ` |

The last two are used in `Heyting.Regular` to show that regular elements form a Boolean algebra.

---

## 5. Finset.inf / Finset.sup API

### Key Lemmas Available

All in `Mathlib/Data/Finset/Lattice/Fold.lean`:

| Lemma | Type | Notes |
|-------|------|-------|
| `Finset.inf_insert` | `(insert b s).inf f = f b ⊓ s.inf f` | Requires `[DecidableEq β]`, `[SemilatticeInf α]`, `[OrderTop α]` |
| `Finset.inf_le` | `b ∈ s → s.inf f ≤ f b` | Requires `[SemilatticeInf α]`, `[OrderTop α]` |
| `Finset.inf_sup_distrib_right` | `s.inf f ⊔ a = s.inf (fun i => f i ⊔ a)` | Requires `[DistribLattice α]`, `[OrderTop α]` |
| `Finset.inf_sup_distrib_left` | `a ⊔ s.inf f = s.inf (fun i => a ⊔ f i)` | Requires `[DistribLattice α]`, `[OrderTop α]` |
| `Finset.inf'_sup_distrib_right` | (nonempty variant) | For `Finset.inf'` |

### Usage in xcthulhu's Soundness Proof

xcthulhu uses `Γ.inf (v.interp)` for context interpretation, where `Γ : Ctx Atom` is a `Finset`.
The soundness proof uses:
- `Finset.inf_le hB` -- for the `ass` (assumption) case
- `Finset.inf_insert` -- for the `implI` and `disjE` cases
- `inf_sup_right` -- (lattice lemma) for the `disjE` case

**Important**: `Finset.inf` requires `OrderTop α`, which `GeneralizedHeytingAlgebra` provides.
This is why xcthulhu can use `Finset.inf` at the GHA level (for MPL soundness).

**CSLib's current approach** uses `List` contexts (not `Finset`), so the `Finset.inf` API is
not directly needed. However, if CSLib adopts xcthulhu's natural deduction with `Finset` contexts,
these lemmas become essential.

---

## 6. Regular Elements and BooleanAlgebra.ofRegular

### Status: FULLY IN MATHLIB

**File**: `Mathlib/Order/Heyting/Regular.lean` (Yaeel Dillies)

### API

| Definition/Lemma | Type |
|-------------------|------|
| `Heyting.IsRegular a` | `Prop` := `aᶜᶜ = a` |
| `Heyting.Regular α` | `Type` := `{a : α // IsRegular a}` |
| `BooleanAlgebra.ofRegular` | `(forall a, IsRegular (a ⊔ aᶜ)) → BooleanAlgebra α` |
| `Heyting.Regular.lattice` | `Lattice (Regular α)` (via `GaloisInsertion`) |
| `Heyting.Regular.BooleanAlgebra` | `BooleanAlgebra (Regular α)` |
| `Heyting.Regular.toRegular` | `α →o Regular α` (regularization map) |
| `Heyting.Regular.gi` | `GaloisInsertion toRegular (↑)` |

### How xcthulhu Uses It

In `Cslib/Logics/Propositional/Semantics/Heyting.lean`:

```lean
def propBooleanOfLE [Bot Atom] (h : CPL ≤ T) :
    BooleanAlgebra (Quotient T.propositionSetoid) := by
  let iH : HeytingAlgebra (Quotient T.propositionSetoid) := propHeytingOfLE (ipl_le_cpl.trans h)
  refine BooleanAlgebra.ofRegular <| Quotient.ind fun A => ?_
  simp_rw [Heyting.IsRegular, ...]
  -- Shows that double negation elimination (from CPL) makes all elements regular
```

The idea: for a classical theory, all elements of the Lindenbaum quotient are regular
(because `¬¬A → A` is derivable), so `BooleanAlgebra.ofRegular` applies.

### Recommendation

This is the correct approach for the CPL tier. The chain is:
1. Build `HeytingAlgebra` on Lindenbaum quotient (from IPL axioms)
2. Show all elements are regular (from DNE / Peirce's law)
3. Apply `BooleanAlgebra.ofRegular` to get `BooleanAlgebra`

---

## 7. JohanssonAlgebra / Minimal Logic Tier

### Status: NOT IN MATHLIB -- Must Be Defined

**Searches performed**:
- `lean_local_search "JohanssonAlgebra"` -- 0 results
- `lean_local_search "MinimalLogic"` -- 0 results

**What's needed**: A `JohanssonAlgebra` typeclass that sits between `GeneralizedHeytingAlgebra`
and `HeytingAlgebra`. Mathematically, a Johansson algebra (also called a pseudo-complemented
lattice or minimal Heyting algebra) is a distributive lattice with top, bottom, and `⇨`
satisfying the GHA adjunction, but NOT requiring `a ⇨ ⊥ = aᶜ` (the complement is primitive
or absent).

**Option A**: Define `JohanssonAlgebra` as `GeneralizedHeytingAlgebra` + `OrderBot`.
This is essentially `HeytingAlgebra` without the `himp_bot` axiom and without `Compl`.

**Option B**: Use `GeneralizedHeytingAlgebra` directly for MPL and just pass `bot_val` explicitly
(CSLib's current approach in `AlgEvaluate`).

**Recommendation**: Option A is cleaner mathematically. `JohanssonAlgebra` would be:
```lean
class JohanssonAlgebra (α : Type*) extends GeneralizedHeytingAlgebra α, OrderBot α
```
No complement operation, no `himp_bot` axiom. This is a conservative extension of
`GeneralizedHeytingAlgebra` and a strict superclass of `HeytingAlgebra`.

---

## 8. Summary: Mathlib API Availability

| Component | Status | Location |
|-----------|--------|----------|
| `GeneralizedHeytingAlgebra` | IN MATHLIB | `Order.Heyting.Basic` |
| `HeytingAlgebra` | IN MATHLIB | `Order.Heyting.Basic` |
| `BooleanAlgebra` | IN MATHLIB | `Order.BooleanAlgebra.Defs` |
| `HeytingHom` / `HeytingHomClass` | IN MATHLIB | `Order.Heyting.Hom` |
| `GeneralizedHeytingHom` | IN XCTHULHU | `ForMathlib/Order/Heyting/Hom.lean` |
| `HImpHom` | IN XCTHULHU | `ForMathlib/Order/Heyting/Hom.lean` |
| `LatticeCon` | IN MATHLIB | `Order.Lattice.Congruence` |
| `BooleanAlgebra.ofRegular` | IN MATHLIB | `Order.Heyting.Regular` |
| `Heyting.Regular` + BA instance | IN MATHLIB | `Order.Heyting.Regular` |
| Dedekind-MacNeille completion | IN XCTHULHU | `Semantics/DedekindMacneille.lean` |
| `DedekindMacNeilleCompletion.coe_himp` | IN XCTHULHU | Same file |
| `Finset.inf_insert`, `Finset.inf_le` | IN MATHLIB | `Data.Finset.Lattice.Fold` |
| `Order.Ideal`, `Order.PFilter` | IN MATHLIB | `Order.Ideal`, `Order.PFilter` |
| Prime ideal separation | IN XCTHULHU | `ForMathlib/Order/PrimeSeparator.lean` |
| `JohanssonAlgebra` | NOT ANYWHERE | Must define (~5 lines) |
| Lindenbaum quotient construction | IN XCTHULHU | `Semantics/Heyting.lean` |

## 9. Gaps Requiring New Code

### Must Build (not in Mathlib)

1. **JohanssonAlgebra typeclass** (~5 lines): `GeneralizedHeytingAlgebra` + `OrderBot` without
   `Compl` or `himp_bot`.

2. **Dedekind-MacNeille completion** (~500 lines, from xcthulhu): Closure operator approach,
   CompleteLattice instance, HeytingAlgebra instance, order embedding, simp lemmas.

3. **Lindenbaum quotient** (~300 lines, from xcthulhu): Manual quotient construction with
   `Quotient.lift₂` for all operations, PartialOrder -> Lattice -> GHA -> HA -> BA chain.

4. **ForMathlib hom types** (~200 lines, from xcthulhu): `HImpHom`, `GeneralizedHeytingHom`,
   `GeneralizedHeytingHomClass`.

5. **Prime ideal/filter separation** (~200 lines, from xcthulhu): Zorn's lemma argument for
   extending proper ideals to prime ideals in distributive lattices.

### Already Available (no new code needed)

1. All Heyting algebra simp lemmas for soundness proofs
2. `HeytingHom` with full API for IPL/CPL homomorphism arguments
3. `BooleanAlgebra.ofRegular` for the CPL tier upgrade
4. `LatticeCon` for potential alternative quotient approach
5. `Finset.inf` API for context interpretation

## 10. Tactic Survey Results

For the algebraic soundness proofs, the following tactic patterns are effective (verified by
reading CSLib's existing `Algebra/Soundness.lean`):

| Proof Goal | Tactic Chain |
|------------|-------------|
| `a ⇨ b = ⊤` (validity) | `rw [himp_eq_top_iff]` then lattice reasoning |
| Modus ponens soundness | `himp_inf_le` with `le_inf` |
| Distributivity cases | `inf_sup_left` / `inf_sup_right` |
| Ex falso (HA) | `bot_le` |
| Peirce's law (BA) | `simp [himp_eq, compl_sup, compl_compl]` |
| Context membership | `Finset.inf_le hB` |
| Context extension | `Finset.inf_insert` |

The existing proofs in CSLib are clean and use minimal tactic chains. The Mathlib API is
well-suited for these proofs.
