/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Mathlib.Order.Heyting.Basic

/-! # Brouwerian Semilattices

A **Brouwerian semilattice** is an algebraic structure capturing the
conjunction-implication-verum fragment `{⊓, ⇨, ⊤}` of intuitionistic logic, without
requiring a join operation `⊔`. It is the weakest class in which the adjunction

  `a ≤ b ⇨ c ↔ a ⊓ b ≤ c`

holds, and fills the gap between `SemilatticeInf` and `GeneralizedHeytingAlgebra` in
Mathlib's typeclass hierarchy. A `GeneralizedHeytingAlgebra` (which requires `Lattice`) is a
special case where join is also available.

The term "Brouwerian semilattice" follows Köhler (1981) and Nemitz (1965), who studied these
algebras as the algebraic counterpart to the implication-conjunction fragment of intuitionistic
propositional logic. The alternative name "implicative semilattice" (Nemitz) is also standard.

## Main Definitions

- `BrouwerianSemilattice`: typeclass extending `SemilatticeInf`, `OrderTop`, and `HImp` with
  the adjunction axiom `le_himp_iff`.
- `BrouwerianSemilattice.ofHImp`: convenience constructor for building instances from a raw
  `himp` function when `HImp` is not yet registered.
- `GeneralizedHeytingAlgebra.toBrouwerianSemilattice`: forgetful instance from GHA, at
  priority 100 to avoid preference over direct `BrouwerianSemilattice` instances.

## Algebraic Theory

The adjunction `a ≤ b ⇨ c ↔ a ⊓ b ≤ c` yields approximately 20 lemmas in the
`BrouwerianSemilattice` namespace, analogous to the GHA lemmas in Mathlib, including:
- Core adjunction variants: `BrouwerianSemilattice.le_himp_iff'`, `le_himp_comm`
- Basic identities: `himp_self`, `top_himp`, `himp_top`, `himp_eq_top_iff`
- Modus ponens: `himp_inf_le`, `inf_himp_le`
- Currying: `himp_himp`, `himp_left_comm`, `himp_idem`
- Monotonicity: `himp_le_himp_left`, `himp_le_himp_right`, `himp_le_himp`
- Distribution: `himp_inf_distrib`
- Galois connection: `gc_inf_himp`

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

/-- A **Brouwerian semilattice** is a meet-semilattice with top and Heyting implication
satisfying the adjunction `a ≤ b ⇨ c ↔ a ⊓ b ≤ c`.

This is the weakest structure supporting the `{⊓, ⇨, ⊤}` fragment of intuitionistic logic,
without requiring a join operation. Every `GeneralizedHeytingAlgebra` is a Brouwerian
semilattice via the forgetful instance `GeneralizedHeytingAlgebra.toBrouwerianSemilattice`. -/
class BrouwerianSemilattice (α : Type*) extends SemilatticeInf α, OrderTop α, HImp α where
  /-- The adjunction axiom: `a ≤ b ⇨ c` if and only if `a ⊓ b ≤ c`. -/
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c

namespace BrouwerianSemilattice

/-- Construct a `BrouwerianSemilattice` from a raw `himp` function satisfying the adjunction,
analogous to `HeytingAlgebra.ofHImp`. -/
abbrev ofHImp [SemilatticeInf α] [OrderTop α]
    (himp : α → α → α)
    (le_himp_iff : ∀ a b c : α, a ≤ himp b c ↔ a ⊓ b ≤ c) :
    BrouwerianSemilattice α :=
  { ‹SemilatticeInf α›, ‹OrderTop α›, (⟨himp⟩ : HImp α) with
    le_himp_iff := le_himp_iff }

section

variable {α : Type*} [BrouwerianSemilattice α] {a b c d : α}

/-! ### Core adjunction variants -/

/-- The adjunction `a ≤ b ⇨ c` iff `b ⊓ a ≤ c`, with the order of `⊓` swapped. -/
theorem le_himp_iff' : a ≤ b ⇨ c ↔ b ⊓ a ≤ c := by
  rw [BrouwerianSemilattice.le_himp_iff, inf_comm]

/-- Commutativity of the arguments of `⇨` in the adjunction: `a ≤ b ⇨ c ↔ b ≤ a ⇨ c`. -/
theorem le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by
  rw [BrouwerianSemilattice.le_himp_iff, le_himp_iff', inf_comm]

/-! ### Basic identities -/

/-- `a ⇨ a = ⊤`: every element implies itself. -/
@[simp]
theorem himp_self (a : α) : a ⇨ a = ⊤ := by
  apply le_antisymm le_top
  rw [BrouwerianSemilattice.le_himp_iff]
  exact inf_le_right

/-- `⊤ ⇨ a = a`: implication from top is the identity. -/
@[simp]
theorem top_himp (a : α) : ⊤ ⇨ a = a := by
  apply le_antisymm
  · have h := (BrouwerianSemilattice.le_himp_iff (⊤ ⇨ a) ⊤ a).mp le_rfl
    simpa using h
  · rw [BrouwerianSemilattice.le_himp_iff]
    simp

/-- `a ⇨ ⊤ = ⊤`: everything implies top. -/
@[simp]
theorem himp_top (a : α) : a ⇨ ⊤ = ⊤ := by
  apply le_antisymm le_top
  rw [BrouwerianSemilattice.le_himp_iff]
  exact le_top

/-- `a ⇨ b = ⊤ ↔ a ≤ b`: the Heyting deduction theorem. -/
@[simp]
theorem himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b := by
  constructor
  · intro h
    have h₁ := (BrouwerianSemilattice.le_himp_iff ⊤ a b).mp (h.symm ▸ le_rfl)
    simpa using h₁
  · intro h
    apply le_antisymm le_top
    rw [BrouwerianSemilattice.le_himp_iff]
    exact le_trans inf_le_right h

/-- Weakening: `a ≤ b ⇨ a`. -/
theorem le_himp (a b : α) : a ≤ b ⇨ a := by
  rw [BrouwerianSemilattice.le_himp_iff]
  exact inf_le_left

/-- Self-implication: `a ≤ a ⇨ b ↔ a ≤ b`. -/
theorem le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by
  rw [BrouwerianSemilattice.le_himp_iff, inf_idem]

/-! ### Modus ponens and interaction -/

/-- Modus ponens: `(a ⇨ b) ⊓ a ≤ b`. -/
theorem himp_inf_le : (a ⇨ b) ⊓ a ≤ b := by
  exact (BrouwerianSemilattice.le_himp_iff (a ⇨ b) a b).mp le_rfl

/-- Modus ponens, commutativity variant: `a ⊓ (a ⇨ b) ≤ b`. -/
theorem inf_himp_le : a ⊓ (a ⇨ b) ≤ b := by
  rw [inf_comm]; exact himp_inf_le

/-- Interaction: `a ⊓ (a ⇨ b) = a ⊓ b`. -/
@[simp]
theorem inf_himp : a ⊓ (a ⇨ b) = a ⊓ b := by
  apply le_antisymm
  · exact le_inf inf_le_left inf_himp_le
  · apply inf_le_inf_left
    exact (BrouwerianSemilattice.le_himp_iff b a b).mpr inf_le_left

/-- Interaction, swapped: `(a ⇨ b) ⊓ a = b ⊓ a`. -/
@[simp]
theorem himp_inf_self : (a ⇨ b) ⊓ a = b ⊓ a := by
  rw [inf_comm, inf_himp, inf_comm]

/-! ### Currying and composition -/

/-- Currying: `a ⇨ b ⇨ c = (a ⊓ b) ⇨ c`. -/
theorem himp_himp (a b c : α) : a ⇨ b ⇨ c = (a ⊓ b) ⇨ c := by
  apply le_antisymm
  · rw [BrouwerianSemilattice.le_himp_iff]
    -- Goal: (a ⇨ b ⇨ c) ⊓ (a ⊓ b) ≤ c
    -- Use: (a ⇨ b ⇨ c) ⊓ a ≤ b ⇨ c, then ((a ⇨ b ⇨ c) ⊓ a) ⊓ b ≤ c
    have h1 : (a ⇨ b ⇨ c) ⊓ a ≤ b ⇨ c :=
      (BrouwerianSemilattice.le_himp_iff (a ⇨ b ⇨ c) a (b ⇨ c)).mp le_rfl
    have h2 : ((a ⇨ b ⇨ c) ⊓ a) ⊓ b ≤ c :=
      (BrouwerianSemilattice.le_himp_iff _ b c).mp h1
    calc (a ⇨ b ⇨ c) ⊓ (a ⊓ b)
        = (a ⇨ b ⇨ c) ⊓ a ⊓ b := by rw [← inf_assoc]
      _ ≤ c := h2
  · rw [BrouwerianSemilattice.le_himp_iff]
    -- Goal: (a ⊓ b ⇨ c) ⊓ a ≤ b ⇨ c
    rw [BrouwerianSemilattice.le_himp_iff]
    -- Goal: (a ⊓ b ⇨ c) ⊓ a ⊓ b ≤ c
    have h3 : (a ⊓ b ⇨ c) ⊓ (a ⊓ b) ≤ c :=
      (BrouwerianSemilattice.le_himp_iff (a ⊓ b ⇨ c) (a ⊓ b) c).mp le_rfl
    calc (a ⊓ b ⇨ c) ⊓ a ⊓ b
        = (a ⊓ b ⇨ c) ⊓ (a ⊓ b) := by rw [inf_assoc]
      _ ≤ c := h3

/-- Commutativity of currying: `a ⇨ b ⇨ c = b ⇨ a ⇨ c`. -/
theorem himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by
  rw [himp_himp, himp_himp, inf_comm]

/-- Idempotence: `b ⇨ b ⇨ a = b ⇨ a`. -/
theorem himp_idem : b ⇨ b ⇨ a = b ⇨ a := by
  rw [himp_himp, inf_idem]

/-- Triangle inequality (transitivity): `(a ⇨ b) ⊓ (b ⇨ c) ≤ a ⇨ c`. -/
theorem himp_triangle : (a ⇨ b) ⊓ (b ⇨ c) ≤ a ⇨ c := by
  rw [BrouwerianSemilattice.le_himp_iff]
  have step1 : (a ⇨ b) ⊓ (b ⇨ c) ⊓ a ≤ (a ⇨ b) ⊓ a := by
    apply inf_le_inf_right; exact inf_le_left
  have step2 : (a ⇨ b) ⊓ a ≤ b := himp_inf_le
  have step3 : b ≤ b := le_rfl
  have step4 : (a ⇨ b) ⊓ (b ⇨ c) ⊓ a ≤ b ⇨ c :=
    le_trans inf_le_left inf_le_right
  have step5 : b ⊓ (b ⇨ c) ≤ c := inf_himp_le
  calc (a ⇨ b) ⊓ (b ⇨ c) ⊓ a
      ≤ b ⊓ (b ⇨ c) := le_inf (le_trans step1 step2) step4
    _ ≤ c := step5

/-- Contraposition base: `a ≤ (a ⇨ b) ⇨ b`. -/
theorem le_himp_himp : a ≤ (a ⇨ b) ⇨ b := by
  rw [BrouwerianSemilattice.le_himp_iff, inf_comm]
  exact himp_inf_le

/-! ### Monotonicity -/

/-- `⇨` is monotone in the second argument. -/
theorem himp_le_himp_left (h : a ≤ b) : c ⇨ a ≤ c ⇨ b := by
  rw [BrouwerianSemilattice.le_himp_iff]
  exact le_trans himp_inf_le h

/-- `⇨` is antitone in the first argument. -/
theorem himp_le_himp_right (h : a ≤ b) : b ⇨ c ≤ a ⇨ c := by
  rw [BrouwerianSemilattice.le_himp_iff]
  exact le_trans (inf_le_inf_left (b ⇨ c) h) himp_inf_le

/-- `⇨` is monotone in the second argument and antitone in the first.

Used with `@[gcongr]` for automated monotonicity reasoning. -/
@[gcongr]
theorem himp_le_himp (h₁ : a ≤ b) (h₂ : c ≤ d) : b ⇨ c ≤ a ⇨ d :=
  le_trans (himp_le_himp_right h₁) (himp_le_himp_left h₂)

/-! ### Distribution -/

/-- `⇨` distributes over `⊓` in the codomain: `a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c)`. -/
theorem himp_inf_distrib (a b c : α) : a ⇨ b ⊓ c = (a ⇨ b) ⊓ (a ⇨ c) := by
  apply le_antisymm
  · exact le_inf (himp_le_himp_left inf_le_left) (himp_le_himp_left inf_le_right)
  · rw [BrouwerianSemilattice.le_himp_iff]
    apply le_inf
    · exact le_trans (inf_le_inf_right _ inf_le_left) himp_inf_le
    · exact le_trans (inf_le_inf_right _ inf_le_right) himp_inf_le

/-! ### Galois connection -/

/-- The adjunction `a ≤ b ⇨ c ↔ a ⊓ b ≤ c` is a Galois connection between `(b ⊓ ·)` and
`(b ⇨ ·)`, i.e., `inf b` and `himp b` form an adjoint pair. -/
theorem gc_inf_himp (b : α) : GaloisConnection (b ⊓ ·) (b ⇨ ·) := by
  intro a c
  rw [BrouwerianSemilattice.le_himp_iff, inf_comm]

end

end BrouwerianSemilattice

/-- Every `GeneralizedHeytingAlgebra` is a Brouwerian semilattice, obtained by forgetting the
join. Priority 100 follows the Mathlib convention (see note [lower instance priority]) to
avoid preference over a direct `BrouwerianSemilattice` instance. -/
instance (priority := 100) GeneralizedHeytingAlgebra.toBrouwerianSemilattice
    [GeneralizedHeytingAlgebra α] : BrouwerianSemilattice α where
  le_himp_iff := GeneralizedHeytingAlgebra.le_himp_iff

/-! ## Prod and Pi instances -/

/-- The product of two Brouwerian semilattices is a Brouwerian semilattice, with operations
applied componentwise. -/
instance Prod.instBrouwerianSemilattice [BrouwerianSemilattice α] [BrouwerianSemilattice β] :
    BrouwerianSemilattice (α × β) where
  le_himp_iff a b c := by
    simp [BrouwerianSemilattice.le_himp_iff, Prod.le_def]

/-- A product type of Brouwerian semilattices indexed by `ι` is a Brouwerian semilattice,
with operations applied pointwise. -/
instance Pi.instBrouwerianSemilattice {ι : Type*} {α : ι → Type*}
    [∀ i, BrouwerianSemilattice (α i)] : BrouwerianSemilattice (∀ i, α i) where
  le_himp_iff a b c := by
    simp [BrouwerianSemilattice.le_himp_iff, Pi.le_def]
