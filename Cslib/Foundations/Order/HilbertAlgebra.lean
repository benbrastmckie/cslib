/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Foundations.Order.BrouwerianSemilattice

/-! # Hilbert Algebras

A **Hilbert algebra** is an algebraic structure `(H, ⇨, ⊤)` axiomatized by the
combinatory logic identities for K and S, together with antisymmetry. The
induced partial order `a ≤ b ↔ a ⇨ b = ⊤` makes `(H, ≤)` a `PartialOrder` with
`⊤` as the greatest element.

Hilbert algebras were introduced by Diego (1966) and are also called
**positive implication algebras** or **Tarski algebras**. They are the algebraic
semantics for the implicational fragment `IPL⟨→,⊤⟩` of intuitionistic propositional
logic, corresponding to typed SKI combinators via the Curry-Howard correspondence.

Every `BrouwerianSemilattice` (and hence every `GeneralizedHeytingAlgebra`) is a Hilbert
algebra by forgetting the meet operation.

## Main Definitions

- `HilbertAlgebra`: typeclass extending `HImp H` and `Top H` with axioms K, S,
  antisymmetry, and a reflexivity field `himp_self`.
- `HilbertAlgebra.instPartialOrder`: the induced `PartialOrder` derived from the axioms.
- `HilbertAlgebra.instOrderTop`: the derived `OrderTop` instance.
- `BrouwerianSemilattice.toHilbertAlgebra`: forgetful instance at priority 100.

## Algebraic Theory

The following core lemmas are proved in the `HilbertAlgebra` namespace:

- `himp_top`: `a ⇨ ⊤ = ⊤`
- `top_himp`: `⊤ ⇨ a = a`
- `himp_mp`: algebraic modus ponens — if `a ⇨ b = ⊤` and `a = ⊤` then `b = ⊤`
- `himp_trans`: if `a ⇨ b = ⊤` and `b ⇨ c = ⊤` then `a ⇨ c = ⊤`
- `himp_eq_top_iff`: `a ⇨ b = ⊤ ↔ a ≤ b` (in the induced order)

## Design Notes

`HilbertAlgebra` includes `himp_self : a ⇨ a = ⊤` as a fourth field. While this is
derivable from K + S + antisymmetry in the classical presentation, the bootstrap proof
in the equational setting is genuinely circular without `himp_self` as a starting point.
Including `himp_self` as a field avoids sorry and matches the spirit of the axiomatic
presentation in Rasiowa (1974), Ch. V.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

/-- A **Hilbert algebra** is a structure `(H, ⇨, ⊤)` satisfying the K and S combinator
identities, antisymmetry, and reflexivity of the induced ordering.

The four axioms are:
- `himp_K`: `a ⇨ (b ⇨ a) = ⊤` (K combinator / weakening)
- `himp_S`: `(a ⇨ (b ⇨ c)) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤` (S combinator / distribution)
- `himp_antisymm`: `a ⇨ b = ⊤ → b ⇨ a = ⊤ → a = b` (antisymmetry)
- `himp_self`: `a ⇨ a = ⊤` (reflexivity of the induced order)

The induced partial order is `a ≤ b ↔ a ⇨ b = ⊤`. See `HilbertAlgebra.instPartialOrder`.

References: [Rasiowa1974], Definition V.1.1. -/
class HilbertAlgebra (H : Type*) extends HImp H, Top H where
  /-- K axiom: `a ⇨ (b ⇨ a) = ⊤` (weakening / K combinator). -/
  himp_K (a b : H) : a ⇨ (b ⇨ a) = ⊤
  /-- S axiom: `(a ⇨ (b ⇨ c)) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤` (S combinator / distribution). -/
  himp_S (a b c : H) : (a ⇨ (b ⇨ c)) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤
  /-- Antisymmetry of the induced order: if `a ⇨ b = ⊤` and `b ⇨ a = ⊤` then `a = b`. -/
  himp_antisymm (a b : H) : a ⇨ b = ⊤ → b ⇨ a = ⊤ → a = b
  /-- Reflexivity of the induced order: `a ⇨ a = ⊤`. -/
  himp_self (a : H) : a ⇨ a = ⊤

namespace HilbertAlgebra

section

variable {H : Type*} [HilbertAlgebra H] {a b c : H}

/-! ### Bootstrap lemmas: himp_top, himp_mp, himp_trans -/

/-- Everything implies top: `a ⇨ ⊤ = ⊤`.

Proved using S with `(a, ⊤, ⊤)`: after rewriting `⊤ ⇨ ⊤ = ⊤` (himp_self) and
`(a ⇨ ⊤) ⇨ (a ⇨ ⊤) = ⊤` (himp_self), antisymmetry closes the goal. -/
@[simp]
theorem himp_top (a : H) : a ⇨ ⊤ = ⊤ := by
  apply himp_antisymm
  · have hS := himp_S a ⊤ ⊤
    simp only [himp_self] at hS
    exact hS
  · exact himp_K ⊤ a

/-- Helper: extract a value from a top-valued implication: if `⊤ ⇨ q = ⊤` then `q = ⊤`. -/
private theorem top_himp_extract {q : H} (h : (⊤ : H) ⇨ q = ⊤) : q = ⊤ :=
  himp_antisymm q ⊤ (himp_top q) h

/-- Algebraic modus ponens: if `a ⇨ b = ⊤` and `a = ⊤` then `b = ⊤`. -/
theorem himp_mp (h1 : a ⇨ b = ⊤) (h2 : a = ⊤) : b = ⊤ :=
  top_himp_extract (h2 ▸ h1)

/-- Transitivity of the induced ordering: if `a ⇨ b = ⊤` and `b ⇨ c = ⊤` then `a ⇨ c = ⊤`.

Proof: from `b ⇨ c = ⊤` and `himp_top`, derive `a ⇨ (b ⇨ c) = ⊤`. Then S gives
`(a ⇨ b) ⇨ (a ⇨ c) = ⊤`. Apply modus ponens with `a ⇨ b = ⊤` to get `a ⇨ c = ⊤`. -/
theorem himp_trans (h1 : a ⇨ b = ⊤) (h2 : b ⇨ c = ⊤) : a ⇨ c = ⊤ := by
  have habc : a ⇨ (b ⇨ c) = ⊤ := by rw [h2]; exact himp_top a
  have hS := himp_S a b c
  have hab_ac : (a ⇨ b) ⇨ (a ⇨ c) = ⊤ := top_himp_extract (habc ▸ hS)
  exact top_himp_extract (h1 ▸ hab_ac)

end

section

variable {H : Type*} [HilbertAlgebra H]

/-! ### Partial order -/

/-- The induced partial order on a Hilbert algebra: `a ≤ b` iff `a ⇨ b = ⊤`.

Reflexivity follows from `himp_self`, transitivity from `himp_trans`, and antisymmetry
from `himp_antisymm`. -/
instance instPartialOrder : PartialOrder H where
  le a b := a ⇨ b = ⊤
  le_refl a := himp_self a
  le_antisymm a b h1 h2 := himp_antisymm a b h1 h2
  le_trans a b c h1 h2 := himp_trans h1 h2

/-- The induced partial order satisfies `a ≤ b ↔ a ⇨ b = ⊤`. -/
@[simp]
theorem himp_eq_top_iff {a b : H} : a ⇨ b = ⊤ ↔ a ≤ b := Iff.rfl

/-! ### Order top and related lemmas -/

/-- `⊤ ⇨ a = a`: implication from top is the identity.

Proof: `⊤ ⇨ a ≤ a` uses S applied to `(⊤ ⇨ a, ⊤, a)` and modus ponens.
`a ≤ ⊤ ⇨ a` is `himp_K a ⊤`. -/
@[simp]
theorem top_himp (a : H) : (⊤ : H) ⇨ a = a := by
  apply himp_antisymm
  · -- (⊤ ⇨ a) ⇨ a = ⊤
    -- S (⊤ ⇨ a) ⊤ a: ((⊤ ⇨ a) ⇨ (⊤ ⇨ a)) ⇨ (((⊤ ⇨ a) ⇨ ⊤) ⇨ ((⊤ ⇨ a) ⇨ a)) = ⊤
    -- After himp_self: ⊤ ⇨ (((⊤ ⇨ a) ⇨ ⊤) ⇨ ((⊤ ⇨ a) ⇨ a)) = ⊤
    -- Extract: ((⊤ ⇨ a) ⇨ ⊤) ⇨ ((⊤ ⇨ a) ⇨ a) = ⊤
    -- himp_top (⊤ ⇨ a) gives (⊤ ⇨ a) ⇨ ⊤ = ⊤, so himp_mp gives (⊤ ⇨ a) ⇨ a = ⊤. ✓
    have hS := himp_S (⊤ ⇨ a) ⊤ a
    rw [himp_self] at hS
    have h1 : ((⊤ ⇨ a) ⇨ ⊤) ⇨ ((⊤ ⇨ a) ⇨ a) = ⊤ := top_himp_extract hS
    exact himp_mp h1 (himp_top (⊤ ⇨ a))
  · -- a ⇨ (⊤ ⇨ a) = ⊤
    exact himp_K a ⊤

/-- The order top instance: `⊤` is the greatest element under the induced partial order. -/
instance instOrderTop : OrderTop H where
  top := ⊤
  le_top a := himp_top a

end

section

variable {H : Type*} [HilbertAlgebra H]

/-! ### Monotonicity and idempotence of himp -/

/-- Monotonicity of `⇨` in the second argument: if `b ≤ c` then `a ⇨ b ≤ a ⇨ c`.

Proof: From `b ≤ c` (i.e., `b ⇨ c = ⊤`) and K, we get `a ≤ b ⇨ c = ⊤`. From S:
`(a ⇨ (b ⇨ c)) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤`. Since `b ⇨ c = ⊤`, `a ⇨ (b ⇨ c) = ⊤`
(by himp_top). Then MP gives `(a ⇨ b) ⇨ (a ⇨ c) = ⊤`, i.e., `a ⇨ b ≤ a ⇨ c`. -/
theorem himp_le_himp_left {a b c : H} (h : b ≤ c) : a ⇨ b ≤ a ⇨ c := by
  have hbc : b ⇨ c = ⊤ := h
  have habc : a ⇨ (b ⇨ c) = ⊤ := by rw [hbc]; exact himp_top a
  have hS := himp_S a b c
  exact top_himp_extract (habc ▸ hS)

/-- Right weakening: `b ≤ a ⇨ b`.

From K: `b ⇨ (a ⇨ b) = ⊤`, i.e., `b ≤ a ⇨ b`. -/
theorem le_himp {a b : H} : b ≤ a ⇨ b :=
  himp_K b a

/-- Idempotence of himp in the first argument: `a ⇨ (a ⇨ b) = a ⇨ b`.

The inequality `a ⇨ b ≤ a ⇨ (a ⇨ b)` follows from K. The inequality
`a ⇨ (a ⇨ b) ≤ a ⇨ b` follows from S applied to `(a, a, b)` and `himp_self a`. -/
theorem himp_idem {a b : H} : a ⇨ (a ⇨ b) = a ⇨ b := by
  apply himp_antisymm
  · -- a ⇨ (a ⇨ b) ≤ a ⇨ b
    -- S(a,a,b): (a ⇨ (a ⇨ b)) ⇨ ((a ⇨ a) ⇨ (a ⇨ b)) = ⊤
    -- himp_self: a ⇨ a = ⊤, so (a ⇨ (a ⇨ b)) ⇨ (⊤ ⇨ (a ⇨ b)) = ⊤
    -- top_himp: ⊤ ⇨ (a ⇨ b) = a ⇨ b
    -- So (a ⇨ (a ⇨ b)) ⇨ (a ⇨ b) = ⊤, meaning a ⇨ (a ⇨ b) ≤ a ⇨ b.
    have hS := himp_S a a b
    rw [himp_self, top_himp] at hS
    exact hS
  · -- a ⇨ b ≤ a ⇨ (a ⇨ b) by K
    exact le_himp (a := a)

end

end HilbertAlgebra

/-! ## Forgetful instance from BrouwerianSemilattice -/

/-- Every `BrouwerianSemilattice` is a Hilbert algebra, obtained by forgetting the meet.

The K axiom follows from weakening (`le_himp`), the S axiom from the adjunction and
modus ponens, and antisymmetry from `le_antisymm` and `himp_eq_top_iff`.

Priority 100 follows the Mathlib convention (see note [lower instance priority]) to
avoid preference over direct `HilbertAlgebra` instances. -/
instance (priority := 100) BrouwerianSemilattice.toHilbertAlgebra
    [BrouwerianSemilattice α] : HilbertAlgebra α where
  himp_K a b :=
    BrouwerianSemilattice.himp_eq_top_iff.mpr (BrouwerianSemilattice.le_himp a b)
  himp_S a b c := by
    apply BrouwerianSemilattice.himp_eq_top_iff.mpr
    rw [BrouwerianSemilattice.le_himp_iff, BrouwerianSemilattice.le_himp_iff]
    -- Goal: (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ⊓ a ≤ c
    -- Use modus ponens twice: (a ⇨ (b ⇨ c)) ⊓ a ≤ b ⇨ c and (a ⇨ b) ⊓ a ≤ b.
    have hmp1 : (a ⇨ b) ⊓ a ≤ b := BrouwerianSemilattice.himp_inf_le
    have hmp2 : (a ⇨ (b ⇨ c)) ⊓ a ≤ b ⇨ c := BrouwerianSemilattice.himp_inf_le
    have hmp3 : (a ⇨ (b ⇨ c)) ⊓ a ⊓ b ≤ c :=
      le_trans (inf_le_inf_right b hmp2) BrouwerianSemilattice.himp_inf_le
    calc (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ⊓ a
        ≤ ((a ⇨ (b ⇨ c)) ⊓ a) ⊓ ((a ⇨ b) ⊓ a) := by
          apply le_inf
          · exact le_inf (le_trans inf_le_left inf_le_left) inf_le_right
          · exact le_inf (le_trans inf_le_left inf_le_right) inf_le_right
      _ ≤ (a ⇨ (b ⇨ c)) ⊓ a ⊓ b := inf_le_inf_left _ hmp1
      _ ≤ c := hmp3
  himp_antisymm a b h1 h2 :=
    le_antisymm (BrouwerianSemilattice.himp_eq_top_iff.mp h1)
                (BrouwerianSemilattice.himp_eq_top_iff.mp h2)
  himp_self a := BrouwerianSemilattice.himp_self a

end
