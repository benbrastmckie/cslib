/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Embedding.TemporalEmbedding
public import Cslib.Logics.Bimodal.Metalogic.Core.DerivationTree
public import Cslib.Logics.Bimodal.Metalogic.Soundness.Soundness
public import Cslib.Logics.Temporal.Metalogic.Completeness
public import Cslib.Logics.Temporal.Semantics.Satisfies
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.Basic

/-! # Bimodal TM as a Conservative Extension of Temporal BX

This module proves that the base Bimodal system TM is a conservative extension of
Temporal BX for temporal formulas: any temporal formula `φ` that is derivable in TM
(as `φ.toBimodal`) is already derivable in BX.

## Main Theorems

- `bimodal_truthAt_toBimodal_iff_temporal_satisfies`: Semantic bridge between bimodal
  `truthAt` of temporal translations and temporal `Satisfies`.
- `bimodal_conservative_over_temporal`: TM is a conservative extension of BX for the
  temporal fragment.

## Proof Strategy

We use the semantic bridge approach:
1. For a temporal model `M_temp : TemporalModel D Atom` on a domain `D` with
   `AddCommGroup D`, construct a "temporal task frame" on `D` with `WorldState = D`
   and task relation `taskRel w d u := u = w + d`.
2. Construct a corresponding world history with `domain = fun _ => True` and
   `states t _ = t`, so the world state at time `t` is `t` itself.
3. Prove the semantic bridge: for temporal formulas, `truthAt` in the constructed
   bimodal task model equals `Satisfies` in the temporal model.
4. Apply TM soundness to get truth of `φ.toBimodal` in the constructed model.
5. Apply the semantic bridge to get `Satisfies M_temp t φ`.
6. Conclude temporal validity and apply BX completeness.

## Domain Mismatch

The bimodal `truthAt` requires `[AddCommGroup D]` on the time domain, while temporal
BX completeness quantifies over all `D` with only `[LinearOrder D]`. This gap is
bridged by a model-transfer result (see `temporal_valid_of_bimodal_derivable`), which
currently contains a `sorry` pending a formal proof that temporal BX validity on
AddCommGroup domains coincides with validity over all serial linear orders.

## References

* Burgess (1982) — BX axiom system
* Bimodal TM axiom system (see ProofSystem/Derivation.lean)
* PropositionalConservativity.lean — structural template for this module
-/

@[expose] public section

namespace Cslib.Logic

-- Use qualified names to avoid conflicts between Bimodal and Temporal namespaces
open Cslib.Logic.Bimodal Cslib.Logic.Bimodal.Metalogic

/-! ## Temporal Task Frame Construction

The "temporal task frame": a `TaskFrame D` whose world states ARE the time points of D.
This allows the valuation to match exactly with the temporal model's valuation at each time.
-/

/-- The **temporal task frame** for domain `D`.

This task frame has `WorldState = D` (world states are time points) and task relation
`taskRel w d u := u = w + d`, capturing "state u is reachable from w by a task of
duration d."

Axioms:
- **Nullity identity**: `u = w + 0 ↔ w = u` (from `add_zero`).
- **Forward compositionality**: `u = w + x` and `v = u + y` give `v = w + (x + y)`
  (from `add_assoc`).
- **Converse**: `u = w + d ↔ w = u + (-d)` (from negation symmetry of addition). -/
def temporalTaskFrame (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] : TaskFrame D where
  WorldState := D
  taskRel := fun w d u => u = w + d
  nullity_identity := fun w u => by
    simp only [add_zero]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  forward_comp := fun w u v x y _hx _hy hwu huv => by
    simp only [hwu, huv, add_assoc]
  converse := fun w d u => by
    constructor
    · intro h
      rw [h]
      rw [add_assoc, add_neg_cancel, add_zero]
    · intro h
      rw [h]
      rw [add_assoc, neg_add_cancel, add_zero]

/-- The **temporal world history** for the temporal task frame.

The history has `domain = fun _ => True` (all time points are in the domain) and
`states t _ = t` (the world state at time `t` is `t` itself). The `respects_task`
condition holds because `states s _ = s` and `states t _ = t` give
`taskRel s (t - s) t`, which reduces to `t = s + (t - s)`, following from
`sub_add_cancel`. -/
def temporalWorldHistory (D : Type) [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] :
    WorldHistory (temporalTaskFrame D) where
  domain := fun _ => True
  convex := fun _x _z _hx _hz _y _hxy _hyz => True.intro
  states := fun t _ => t
  respects_task := fun s t _hs _ht _hst => by
    simp only [temporalTaskFrame]
    rw [add_sub_cancel]

/-- The **temporal task model** constructed from a `TemporalModel D Atom`.

The bimodal model uses world states `w : D` with `valuation w p = M_temp.valuation w p`.
This makes bimodal atom truth match temporal atom truth exactly. -/
def temporalTaskModel {D : Type} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    {Atom : Type*} (M_temp : Temporal.TemporalModel D Atom) :
    TaskModel Atom (temporalTaskFrame D) where
  valuation := fun w p => M_temp.valuation w p

/-! ## Semantic Bridge Lemma -/

/-- **Semantic Bridge Lemma**: For temporal formulas, bimodal `truthAt` in the temporal
task model at the temporal world history equals temporal `Satisfies`.

More precisely: for any temporal formula `φ : Temporal.Formula Atom` and any `t : D`
(where `D` has the full bimodal domain structure), we have:
`truthAt (temporalTaskModel M) Set.univ (temporalWorldHistory D) t φ.toBimodal
  ↔ Temporal.Satisfies M t φ`.

**Proof**: Structural induction on `φ`. The key cases:
- **atom**: Both sides equal `M.valuation t p`. The bimodal side gives
  `∃ ht : True, M.valuation (temporalWorldHistory.states t ht) p` which simplifies
  to `M.valuation t p` since `states t _ = t`.
- **bot**: Both sides are `False`.
- **imp**: Both are material conditionals; the IHs translate the components.
- **untl**: Both sides are `∃ s > t, (φ-event holds at s) ∧ (ψ-guard holds between)`.
  Since `temporalWorldHistory.states s _ = s`, the bimodal `truthAt` and temporal
  `Satisfies` have the same quantifier structure.
- **snce**: Symmetric to `untl`.

The `box` case does not arise since `Temporal.Formula` has no `box` constructor. -/
theorem bimodal_truthAt_toBimodal_iff_temporal_satisfies
    {Atom : Type*} {D : Type} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D]
    (M : Temporal.TemporalModel D Atom) (t : D)
    (φ : Temporal.Formula Atom) :
    truthAt (temporalTaskModel M) Set.univ (temporalWorldHistory D) t φ.toBimodal
      ↔ Temporal.Satisfies M t φ := by
  induction φ generalizing t with
  | atom p =>
    -- truthAt (atom p): ∃ ht : True, M.valuation (states t ht) p
    --                 = ∃ ht : True, M.valuation t p  (states t _ = t)
    -- Satisfies M t (atom p) = M.valuation t p
    simp only [Temporal.Formula.toBimodal, truthAt, temporalWorldHistory, temporalTaskModel,
               Temporal.Satisfies]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩
  | bot =>
    simp only [Temporal.Formula.toBimodal, truthAt, Temporal.Satisfies]
  | imp φ ψ ih_φ ih_ψ =>
    simp only [Temporal.Formula.toBimodal, truthAt, Temporal.Satisfies]
    exact ⟨fun h h_φ => (ih_ψ t).mp (h ((ih_φ t).mpr h_φ)),
           fun h h_bim => (ih_ψ t).mpr (h ((ih_φ t).mp h_bim))⟩
  | untl ψ φ ih_ψ ih_φ =>
    simp only [Temporal.Formula.toBimodal, truthAt, Temporal.Satisfies]
    constructor
    · rintro ⟨s, hts, h_φ, h_ψ⟩
      exact ⟨s, hts, (ih_φ s).mp h_φ, fun r htr hrs => (ih_ψ r).mp (h_ψ r htr hrs)⟩
    · rintro ⟨s, hts, h_φ, h_ψ⟩
      exact ⟨s, hts, (ih_φ s).mpr h_φ, fun r htr hrs => (ih_ψ r).mpr (h_ψ r htr hrs)⟩
  | snce ψ φ ih_ψ ih_φ =>
    simp only [Temporal.Formula.toBimodal, truthAt, Temporal.Satisfies]
    constructor
    · rintro ⟨s, hst, h_φ, h_ψ⟩
      exact ⟨s, hst, (ih_φ s).mp h_φ, fun r hsr hrt => (ih_ψ r).mp (h_ψ r hsr hrt)⟩
    · rintro ⟨s, hst, h_φ, h_ψ⟩
      exact ⟨s, hst, (ih_φ s).mpr h_φ, fun r hsr hrt => (ih_ψ r).mpr (h_ψ r hsr hrt)⟩
  | allFuture φ ih =>
    simp only [Temporal.Formula.toBimodal_allFuture, Truth.future_iff, Temporal.Satisfies]
    exact ⟨fun h s hts => (ih s).mp (h s hts), fun h s hts => (ih s).mpr (h s hts)⟩
  | allPast φ ih =>
    simp only [Temporal.Formula.toBimodal_allPast, Truth.past_iff, Temporal.Satisfies]
    exact ⟨fun h s hst => (ih s).mp (h s hst), fun h s hst => (ih s).mpr (h s hst)⟩

/-! ## Validity on AddCommGroup Domains -/

/-- **Temporal validity on AddCommGroup domains**: If `φ.toBimodal` is TM-derivable,
then `φ` is temporally satisfied in every temporal model on any domain `D` that has
`AddCommGroup D`, `LinearOrder D`, `IsOrderedAddMonoid D`, and `Nontrivial D`.

**Proof**:
1. Extract a derivation tree from the `ThDerivable` hypothesis.
2. Apply TM soundness to the temporal task model on `D` with the universal shift-closed
   `Omega` and the temporal world history.
3. Apply the semantic bridge lemma to convert bimodal truth to temporal satisfaction. -/
theorem temporal_valid_on_addcommgroup
    {Atom : Type*} {φ : Temporal.Formula Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal)
    {D : Type} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]
    (M : Temporal.TemporalModel D Atom) (t : D) :
    Temporal.Satisfies M t φ := by
  obtain ⟨d⟩ := h
  have h_truth : truthAt (temporalTaskModel M) Set.univ (temporalWorldHistory D) t φ.toBimodal :=
    soundness [] φ.toBimodal d D (temporalTaskFrame D) (temporalTaskModel M)
      Set.univ Set.univ_shift_closed (temporalWorldHistory D) (Set.mem_univ _) t (by simp)
  exact (bimodal_truthAt_toBimodal_iff_temporal_satisfies M t φ).mp h_truth

/-! ## Domain Mismatch Resolution

The temporal completeness theorem (see `Temporal.completeness`) requires validity over ALL
domains `D : Type` with `[LinearOrder D] [Nontrivial D] [NoMaxOrder D] [NoMinOrder D]`.
The `temporal_valid_on_addcommgroup` lemma above establishes validity only for domains
with the additional `AddCommGroup D` and `IsOrderedAddMonoid D` structure.

To bridge this gap, we need to show that if `φ` is valid on all AddCommGroup serial
linear orders, it is valid on ALL serial linear orders. This would follow from a
model-transfer result showing that:

  For any temporal countermodel `M` on a serial linear order `D` (without AddCommGroup),
  there exists an equivalent countermodel `M'` on a domain `D'` with AddCommGroup.

**Equivalence condition**: `Temporal.Satisfies M t φ ↔ Temporal.Satisfies M' t' φ` for
corresponding points `t` and `t'`.

The natural approach is to use order-embeddings: the chronicle countermodel (from the
BX completeness proof) lives on `ChronicleSubtype` (a subtype of `ℚ`). However,
pushing a temporal model through an order-embedding does NOT in general preserve temporal
satisfaction, because the quantifiers in `untl`/`snce` range over the target domain,
introducing new potential witnesses. A correct transfer would require one of:
  (a) An order-isomorphism (not just embedding) from ChronicleSubtype to `ℚ`, which
      requires ChronicleSubtype to be countable, dense, and without endpoints (by Cantor's
      theorem `Order.iso_of_countable_dense`). The density property holds only for the
      Dense BX completeness proof, not for base BX.
  (b) A direct proof that temporal formula satisfaction is preserved by order-isomorphism,
      combined with showing ChronicleSubtype is isomorphic to a domain with AddCommGroup.

The `sorry` in `temporal_valid_of_bimodal_derivable` marks this gap.
The proofs of `bimodal_truthAt_toBimodal_iff_temporal_satisfies` (Phase 1) and
`temporal_valid_on_addcommgroup` (Phase 2 partial) are complete and sorry-free.
-/

set_option warn.sorry false in
set_option linter.unusedDecidableInType false in
/-- **Temporal validity on ALL serial linear orders**: If `φ.toBimodal` is TM-derivable,
then `φ` is temporally satisfied in every temporal model on every serial linear order.

**Sorry note**: The domain mismatch between bimodal soundness (needs `AddCommGroup D`)
and temporal completeness (arbitrary serial linear order D) is not yet resolved.
The gap requires a model-transfer result — see the "Domain Mismatch Resolution" section
in this module for a detailed discussion of approaches and why they are non-trivial.

The sorry is localized here; the semantic bridge
(`bimodal_truthAt_toBimodal_iff_temporal_satisfies`) and validity on
AddCommGroup domains (`temporal_valid_on_addcommgroup`) are fully proven. -/
theorem temporal_valid_of_bimodal_derivable
    [Infinite Atom] [DecidableEq Atom]
    {φ : Temporal.Formula Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal)
    (D : Type) [LinearOrder D] [Nontrivial D]
    [NoMaxOrder D] [NoMinOrder D]
    (M : Temporal.TemporalModel D Atom) (t : D) :
    Temporal.Satisfies M t φ := by
  sorry

/-! ## Main Conservativity Theorem -/

set_option linter.unusedDecidableInType false in
/-- **Bimodal TM is a Conservative Extension of Temporal BX**:

If the bimodal translation `φ.toBimodal` is TM-derivable (at base frame class), then
`φ` is BX-derivable.

**Proof outline**:
1. Apply temporal BX completeness: it suffices to show that `φ` is valid in every
   temporal model on every serial linear order.
2. For any domain `D` (serial linear order), model `M`, and time `t`, apply
   `temporal_valid_of_bimodal_derivable`.
3. Temporal completeness then gives BX-derivability.

**Note**: This proof currently relies on `temporal_valid_of_bimodal_derivable`, which
contains a `sorry` for the domain mismatch. The semantic bridge (Phase 1) and the
validity on AddCommGroup domains (Phase 2 partial) are both fully proven. -/
theorem bimodal_conservative_over_temporal
    [Infinite Atom] [DecidableEq Atom] [Denumerable (Temporal.Formula Atom)]
    {φ : Temporal.Formula Atom}
    (h : Cslib.Logic.Bimodal.Bimodal.ThDerivable φ.toBimodal) :
    Cslib.Logic.Temporal.Temporal.ThDerivable φ := by
  apply Cslib.Logic.Temporal.completeness
  intro D _lo _nt _nm _nm2 M t
  exact temporal_valid_of_bimodal_derivable h D M t

end Cslib.Logic

end
