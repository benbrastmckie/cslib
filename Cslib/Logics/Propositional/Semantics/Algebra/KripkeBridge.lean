/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Semantics.Algebra
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal
public import Mathlib.Order.Heyting.Basic

/-! # Kripke–Algebraic Bridge for Intuitionistic Propositional Logic

This module proves that upward-closed sets of a Kripke frame's preorder form a Heyting algebra
and connects `IForces` (Kripke forcing) to `AlgEvaluate` (algebraic evaluation) over this
algebra. This establishes the well-known duality between Kripke semantics and algebraic
semantics for intuitionistic propositional logic.

## Algebraic Representation of Upsets

For a preordered type `World`, the upward-closed sets (upsets) of `World` correspond exactly to
the downward-closed sets (lower sets) of the order dual `OrderDual World`. Mathlib provides a
`HeytingAlgebra` instance for `LowerSet (OrderDual World)` via `Mathlib.Order.UpperLower`, which
we exploit here without defining any new typeclasses.

## Main Definitions

- `UpsetAlgebra World`: type alias for `LowerSet (OrderDual World)`, the Heyting algebra of
  upsets of a preordered type `World`.
- `mkUpset`: constructor lifting an upward-closed predicate to an `UpsetAlgebra` element.
- `upsetVal`: lifts a Kripke valuation `v : World → Atom → Prop` with upward-closure proof to
  an assignment `Atom → UpsetAlgebra World`.
- `upsetBotVal`: lifts a `bot_forces : World → Prop` with upward-closure proof to an element
  of `UpsetAlgebra World`.

## Main Results

- `memMkUpset`: `toDual w ∈ mkUpset P hP ↔ P w` — membership in `mkUpset` unfolds to the
  predicate.
- `upsetHimpChar`: characterizes Heyting implication in `UpsetAlgebra World` as:
  `toDual w ∈ (U ⇨ V) ↔ ∀ w', w ≤ w' → toDual w' ∈ U → toDual w' ∈ V`.
- `kripkeAlgBridge`: the main bridge theorem:
  `IForces v bf w φ ↔ toDual w ∈ AlgEvaluate (upsetVal v hv) (upsetBotVal bf hbf) φ`.
- `iValidOfHAValid`: HA-validity implies intuitionistic Kripke validity (semantic soundness).
- `mValidOfGHAValid`: GHA-validity implies minimal Kripke validity (semantic soundness).

## Design Notes

We use `LowerSet (OrderDual World)` rather than defining a new `UpsetAlgebra` structure because
Mathlib already equips `LowerSet (OrderDual World)` with the `HeytingAlgebra` instance arising
from the complete lattice structure on lower sets. The type alias `UpsetAlgebra World` is purely
for documentation clarity.

The semantic direction proved here (algebraic validity implies Kripke validity) is the soundness
direction of the Kripke–algebraic duality. The converse (Kripke validity implies algebraic
validity) holds but requires the Lindenbaum–Tarski construction and is proved in
`Algebra.Completeness` via the derivability route.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 2.2
* [A. Rasiowa, R. Sikorski, *The Mathematics of Metamathematics*][RasiowaSikorski1963]
-/

@[expose] public section

universe u v

namespace Cslib.Logic.PL

open OrderDual

variable {Atom : Type u} {World : Type v} [Preorder World]

/-! ## The Upset Algebra -/

/-- The Heyting algebra of upsets of a preordered type `World`.

Upward-closed sets of `World` biject with lower sets of `OrderDual World`, and Mathlib provides
a `HeytingAlgebra` instance for `LowerSet (OrderDual World)` from the complete lattice
structure on lower sets. We use this type alias for documentation clarity. -/
abbrev UpsetAlgebra (World : Type*) [Preorder World] : Type _ :=
  LowerSet (OrderDual World)

/-- Construct an element of `UpsetAlgebra World` from an upward-closed predicate.

Given a predicate `P : World → Prop` and a proof that `P` is upward-closed under the preorder
of `World`, `mkUpset P hP` is the corresponding upset in `UpsetAlgebra World`. The carrier is
`{x : OrderDual World | P (ofDual x)}`, and lower-set-ness in `OrderDual World` corresponds to
upward-closure in `World`. -/
def mkUpset (P : World → Prop)
    (hP : ∀ {w w' : World}, w ≤ w' → P w → P w') : UpsetAlgebra World :=
  ⟨{x | P (ofDual x)}, fun _ _ hle ha => hP (toDual_le_toDual.mp hle) ha⟩

/-- Membership in `mkUpset P hP` at `toDual w` is equivalent to `P w`. -/
@[simp]
lemma memMkUpset (P : World → Prop) (hP : ∀ {w w' : World}, w ≤ w' → P w → P w') (w : World) :
    toDual w ∈ mkUpset P hP ↔ P w := by
  simp [mkUpset]

/-- `mkUpset (fun _ => False)` equals the bottom element of `UpsetAlgebra World`. -/
lemma mkUpsetFalse :
    mkUpset (fun _ : World => False) (fun _ h => h) = (⊥ : UpsetAlgebra World) := by
  ext x
  simp [mkUpset, LowerSet.coe_bot]

/-! ## Lifting Kripke Data to the Upset Algebra -/

/-- Lift a Kripke valuation `v : World → Atom → Prop` with upward-closure proof to an
assignment `Atom → UpsetAlgebra World` for algebraic evaluation.

For each atom `p`, `upsetVal v hv p` is the upset of worlds where `p` is forced. -/
def upsetVal
    (v : World → Atom → Prop)
    (hv : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p) :
    Atom → UpsetAlgebra World :=
  fun p => mkUpset (fun w => v w p) (fun hw hp => hv _ hw hp)

/-- Membership in `upsetVal v hv p` at `toDual w` is equivalent to `v w p`. -/
@[simp]
lemma memUpsetVal
    (v : World → Atom → Prop)
    (hv : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (p : Atom) (w : World) :
    toDual w ∈ upsetVal v hv p ↔ v w p := by
  simp [upsetVal]

/-- Lift a `bot_forces : World → Prop` predicate with upward-closure proof to an element of
`UpsetAlgebra World` for algebraic evaluation.

This is the algebraic counterpart of the `botForces` field in a `KripkeModel`. For intuitionistic
logic, where `bot_forces = fun _ => False`, the result is `⊥` in `UpsetAlgebra World`. -/
def upsetBotVal
    (bf : World → Prop)
    (hbf : ∀ {w w' : World}, w ≤ w' → bf w → bf w') :
    UpsetAlgebra World :=
  mkUpset bf hbf

/-- Membership in `upsetBotVal bf hbf` at `toDual w` is equivalent to `bf w`. -/
@[simp]
lemma memUpsetBotVal
    (bf : World → Prop)
    (hbf : ∀ {w w' : World}, w ≤ w' → bf w → bf w')
    (w : World) :
    toDual w ∈ upsetBotVal bf hbf ↔ bf w := by
  simp [upsetBotVal]

/-- `upsetBotVal (fun _ => False)` equals `⊥` in `UpsetAlgebra World`.

This is used in the `iValidOfHAValid` corollary: the intuitionistic Kripke semantics, where
`bot_forces = fun _ => False`, corresponds to the canonical `⊥` of the Heyting algebra. -/
lemma upsetBotValFalse :
    upsetBotVal (fun _ : World => False) (fun _ h => h) = (⊥ : UpsetAlgebra World) :=
  mkUpsetFalse

/-! ## Heyting Implication Characterization -/

/-- Characterization of Heyting implication in `UpsetAlgebra World`.

The Heyting implication `U ⇨ V` in `UpsetAlgebra World` contains `toDual w` iff for every
successor `w'` of `w` (i.e., every `w' ≥ w`), if `toDual w' ∈ U` then `toDual w' ∈ V`. This
matches the Kripke forcing clause for implication exactly.

The proof uses the Heyting adjunction `le_himp_iff` (which says `a ≤ b ⇨ c ↔ a ⊓ b ≤ c`) via
the principal lower set `LowerSet.Iic (toDual w)`. -/
lemma upsetHimpChar (U V : UpsetAlgebra World) (w : World) :
    toDual w ∈ (U ⇨ V : UpsetAlgebra World) ↔
    ∀ w' : World, w ≤ w' → toDual w' ∈ U → toDual w' ∈ V := by
  have key : toDual w ∈ (U ⇨ V : UpsetAlgebra World) ↔
      LowerSet.Iic (toDual w) ⊓ U ≤ V := by
    rw [← le_himp_iff]
    constructor
    · intro h x hx
      simp only [SetLike.mem_coe] at hx
      exact (U ⇨ V).lower hx h
    · intro h
      apply h
      simp only [SetLike.mem_coe, LowerSet.mem_Iic_iff, le_refl]
  rw [key]
  constructor
  · intro h w' hle hu
    apply h
    simp only [LowerSet.coe_inf, LowerSet.coe_Iic, Set.Iic_toDual, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ici, SetLike.mem_coe]
    exact ⟨hle, hu⟩
  · intro h x hx
    simp only [LowerSet.coe_inf, LowerSet.coe_Iic, Set.Iic_toDual, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ici, SetLike.mem_coe] at hx
    exact h (ofDual x) hx.1 hx.2

/-! ## Main Bridge Theorem -/

/-- The Kripke–algebraic bridge theorem for propositional logic.

Kripke forcing `IForces v bf w φ` at world `w` is equivalent to membership of `toDual w` in the
evaluation `AlgEvaluate (upsetVal v hv) (upsetBotVal bf hbf) φ` in the Heyting algebra
`UpsetAlgebra World`.

The proof is by structural induction on the formula `φ`:
- **atom**: Both sides reduce to `v w p` via `memUpsetVal`.
- **bot**: Both sides reduce to `bf w` via `memUpsetBotVal`.
- **imp**: Uses `upsetHimpChar` and the inductive hypotheses; the Kripke clause
  `∀ w' ≥ w, IForces v bf w' φ → IForces v bf w' ψ` matches `toDual w ∈ (eval φ ⇨ eval ψ)`.
- **and**: Uses `LowerSet.coe_inf` (inf = intersection in `UpsetAlgebra World`).
- **or**: Uses `LowerSet.coe_sup` (sup = union in `UpsetAlgebra World`). -/
theorem kripkeAlgBridge
    (v : World → Atom → Prop)
    (bf : World → Prop)
    (hv : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
    (hbf : ∀ {w w' : World}, w ≤ w' → bf w → bf w')
    (w : World) (φ : PL.Proposition Atom) :
    IForces v bf w φ ↔
    toDual w ∈ AlgEvaluate (upsetVal v hv) (upsetBotVal bf hbf) φ := by
  -- Prove ∀ w simultaneously by induction, so the imp case gets the right IH
  suffices h : ∀ (u : World), IForces v bf u φ ↔
      toDual u ∈ AlgEvaluate (upsetVal v hv) (upsetBotVal bf hbf) φ from h w
  induction φ with
  | atom p =>
    intro u; simp [IForces, AlgEvaluate, memUpsetVal]
  | bot =>
    intro u; simp [IForces, AlgEvaluate, memUpsetBotVal]
  | imp φ ψ ihφ ihψ =>
    intro u
    simp only [IForces_imp, AlgEvaluate_imp]
    rw [upsetHimpChar]
    constructor
    · intro h w' hle hφ
      exact (ihψ w').mp (h w' hle ((ihφ w').mpr hφ))
    · intro h w' hle hφ
      exact (ihψ w').mpr (h w' hle ((ihφ w').mp hφ))
  | and φ ψ ihφ ihψ =>
    intro u
    simp only [IForces_and, AlgEvaluate_and, LowerSet.mem_inf_iff]
    exact Iff.and (ihφ u) (ihψ u)
  | or φ ψ ihφ ihψ =>
    intro u
    simp only [IForces_or, AlgEvaluate_or, LowerSet.mem_sup_iff]
    exact Iff.or (ihφ u) (ihψ u)

/-! ## Validity Corollaries -/

/-- Algebraic validity in all Heyting algebras implies intuitionistic Kripke validity.

If `φ` evaluates to `⊤` in every Heyting algebra under every assignment, then `φ` is forced
at every world in every intuitionistic Kripke model. The proof instantiates `HAValid` at the
upset algebra `UpsetAlgebra World` of the Kripke frame: the evaluation at world `w` corresponds
to membership of `toDual w` in the evaluation element, and `⊤ = Set.univ` means every world
forces `φ`.

This is the **semantic soundness** direction: HA-validity is at least as strong as Kripke
validity. -/
theorem iValidOfHAValid {φ : PL.Proposition Atom} (h : HAValid.{u, v} φ) :
    IValid.{u, v} φ := by
  intro World _ val hval w
  -- Instantiate HAValid at UpsetAlgebra World with upsetVal
  have hmem : AlgEvaluate (upsetVal val hval) (⊥ : UpsetAlgebra World) φ = ⊤ :=
    h (UpsetAlgebra World) (upsetVal val hval)
  -- Replace ⊥ with upsetBotVal (fun _ => False) using upsetBotValFalse
  rw [show (⊥ : UpsetAlgebra World) = upsetBotVal (fun _ => False) (fun _ h => h)
    from upsetBotValFalse.symm] at hmem
  -- toDual w ∈ ⊤ = Set.univ, so membership follows from hmem = ⊤
  have hmember : toDual w ∈ AlgEvaluate (upsetVal val hval)
      (upsetBotVal (fun _ : World => False) (fun _ hh => hh)) φ := by
    rw [hmem]; trivial
  exact (kripkeAlgBridge val (fun _ => False) hval (fun _ hh => hh) w φ).mpr hmember

/-- Algebraic validity in all Generalized Heyting algebras implies minimal Kripke validity.

If `φ` evaluates to `⊤` in every GHA under every assignment and every bottom value, then `φ`
is forced at every world in every minimal Kripke model (with arbitrary upward-closed
`bot_forces`). The proof instantiates `GHAValid` at `UpsetAlgebra World` with the appropriate
`upsetBotVal`.

This is the **semantic soundness** direction: GHA-validity implies minimal Kripke validity. -/
theorem mValidOfGHAValid {φ : PL.Proposition Atom} (h : GHAValid.{u, v} φ) :
    MValid.{u, v} φ := by
  intro World _ val bf hval hbf w
  -- Instantiate GHAValid at UpsetAlgebra World with upsetVal and upsetBotVal
  have hmem : AlgEvaluate (upsetVal val hval) (upsetBotVal bf hbf) φ = ⊤ :=
    h (UpsetAlgebra World) (upsetVal val hval) (upsetBotVal bf hbf)
  -- toDual w ∈ ⊤ = Set.univ, which holds trivially
  have hmember : toDual w ∈ AlgEvaluate (upsetVal val hval) (upsetBotVal bf hbf) φ := by
    rw [hmem]; trivial
  exact (kripkeAlgBridge val bf hval hbf w φ).mpr hmember

end Cslib.Logic.PL
