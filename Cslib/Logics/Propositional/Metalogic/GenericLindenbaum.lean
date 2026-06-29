/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem

/-! # Generic Explosion-Parameterized Lindenbaum Substrate

This module provides a generic deductive-closure substrate parameterized by
both the axiom system `Axioms` and a consistency predicate `Cons`. It factors
out the common logic present in `MinLindenbaum` and `IntLindenbaum`:

- `GenericDeductiveClosure Axioms S`: the deductive closure of `S` under `Axioms`.
- `GenericTheory Axioms Cons S`: `Cons S` ∧ deductively closed under `Axioms`.
- `generic_deriv_from_closure_to_S`: compilation lemma (deduction-theorem-based cut-in).
- `generic_deriv_imp_of_union`: union-context cut lemma.
- `generic_imp_witness`: explosion-parameterized implication witness.

## Explosion Parameterization

The single parameter distinguishing minimal logic (no EFQ) from intuitionistic logic
(EFQ required) is the **consistency extension witness** `h_cons_ext`:

```
h_cons_ext : GenericTheory Axioms Cons S → (φ → ψ) ∉ S →
             Cons (GenericDeductiveClosure Axioms (S ∪ {φ}))
```

- **Minimal logic** (`Cons := fun _ => True`): `h_cons_ext = fun _ _ => trivial`.
  Trivially vacuous — no consistency argument needed for the deductive closure.
- **Intuitionistic logic** (`Cons := PropSetConsistent IntPropAxiom`):
  `h_cons_ext` must prove consistency of `GenericDeductiveClosure IntPropAxiom (S ∪ {φ})`,
  which requires:
    (i) EFQ derivation `[¬φ] ⊢ φ → ψ` (via `intNegPhiImpPsi_deriv`) to show
        `PropSetConsistent IntPropAxiom (S ∪ {φ})` when `φ → ψ ∉ S`, and
    (ii) the deductive-closure-preserves-consistency lemma
        (`intDeductiveClosure_consistent`).

This design is described in the task 407 Phase 5 plan.

## Design Notes

This substrate is **active and load-bearing**. Re-instantiation of `MinTheory`/`IntDCCS`
off this substrate was completed in task 407 phase 6 (commit 9242d243). Both consumer
modules import `GenericLindenbaum` and delegate their core Lindenbaum lemmas to the
`generic_*` definitions here via six thin instances:

- `MinLindenbaum.lean` (lines 91, 107, 144): `min_deriv_from_closure_to_S`,
  `min_deriv_imp_of_union`, `min_imp_witness`.
- `IntLindenbaum.lean` (lines 108, 124, 178): `int_deriv_from_closure_to_S`,
  `int_deriv_imp_of_union`, `int_imp_witness`.

The deduction theorem is accessed via explicit `h_implyK`/`h_implyS` witnesses,
consistent with the existing Lindenbaum files and `DeductionTheorem.lean`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 5.1
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## GenericTheory: Axiom- and Consistency-Parameterized Theory -/

/-- A **generic theory** for axiom system `Axioms` with consistency predicate `Cons`.
A set `S` is a `GenericTheory Axioms Cons` iff:
- `Cons S` holds (e.g., trivially `True` for minimal, or `PropSetConsistent` for
  intuitionistic logic), and
- `S` is deductively closed under `Axioms`: any `φ` derivable from finitely many premises
  drawn from `S` also belongs to `S`.

Instantiations:
- `Cons = fun _ => True`: recovers `MinTheory` (no consistency requirement).
- `Cons = PropSetConsistent IntPropAxiom`: recovers `IntDCCS`. -/
def GenericTheory (Axioms : PL.Proposition Atom → Prop)
    (Cons : Set (PL.Proposition Atom) → Prop)
    (S : Set (PL.Proposition Atom)) : Prop :=
  Cons S ∧
  ∀ (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) → (propDerivationSystem Axioms).Deriv L φ → φ ∈ S

/-! ## GenericDeductiveClosure -/

/-- The **generic deductive closure** of a set `S` w.r.t. axiom system `Axioms`:
the set of all `φ` derivable from some finite list of premises drawn from `S`. -/
def GenericDeductiveClosure (Axioms : PL.Proposition Atom → Prop)
    (S : Set (PL.Proposition Atom)) : Set (PL.Proposition Atom) :=
  {φ | ∃ L : List (PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) ∧ (propDerivationSystem Axioms).Deriv L φ}

/-! ## Compilation Lemma (Generic) -/

/-- **Generic compilation lemma**: if every element of `L` is derivable from some
finite list in `S`, then any `φ` derivable from `L` is also derivable from some
finite list in `S`.

The proof proceeds by induction on `L`, using the deduction theorem to "cut" each
element `a` out of the context, replacing it with its witness derivation from `S`.

This is the common body of `min_deriv_from_closure_to_S` (in `MinLindenbaum`) and
`int_deriv_from_closure_to_S` (in `IntLindenbaum`), parameterized over `Axioms`. -/
theorem generic_deriv_from_closure_to_S
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)}
    (L : List (PL.Proposition Atom))
    (hL : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
      (∀ y ∈ Lx, y ∈ S) ∧ (propDerivationSystem Axioms).Deriv Lx x)
    (φ : PL.Proposition Atom)
    (hd : (propDerivationSystem Axioms).Deriv L φ) :
    ∃ L' : List (PL.Proposition Atom),
      (∀ y ∈ L', y ∈ S) ∧ (propDerivationSystem Axioms).Deriv L' φ := by
  induction L generalizing φ with
  | nil => exact ⟨[], fun _ h => (nomatch h), hd⟩
  | cons a L' ih =>
    -- DT: L' ⊢ a → φ
    have hd_dt := hasDeductionTheorem h_implyK h_implyS hd
    -- IH on L' with formula (a → φ)
    obtain ⟨L_imp, hL_imp_sub, hL_imp_deriv⟩ :=
      ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) (a → φ) hd_dt
    -- Witness for a: La ⊆ S with La ⊢ a
    obtain ⟨La, hLa_sub, hLa_deriv⟩ := hL a (List.mem_cons.mpr (Or.inl rfl))
    -- Combine: La ++ L_imp ⊆ S, La ++ L_imp ⊢ φ (by MP)
    exact ⟨La ++ L_imp,
      fun y hy => by
        rw [List.mem_append] at hy
        exact hy.elim (hLa_sub y) (hL_imp_sub y),
      (propDerivationSystem Axioms).mp
        ((propDerivationSystem Axioms).weakening hL_imp_deriv
          (fun x hx => List.mem_append.mpr (Or.inr hx)))
        ((propDerivationSystem Axioms).weakening hLa_deriv
          (fun x hx => List.mem_append.mpr (Or.inl hx)))⟩

/-! ## Union-Context Cut Lemma (Generic) -/

/-- **Generic union cut lemma**: if `L ⊢ ψ` and `L ⊆ S ∪ {φ}`,
then `∃ L' ⊆ S, L' ⊢ φ → ψ`.

Uses `deductionWithMem` + `removeAll` to eliminate all occurrences of `φ`
from the derivation context.

This is the common body of `min_deriv_imp_of_union` (in `MinLindenbaum`) and
`int_deriv_imp_of_union` (in `IntLindenbaum`), parameterized over `Axioms`. -/
theorem generic_deriv_imp_of_union
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)}
    {L : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (hL : ∀ x ∈ L, x ∈ S ∪ {φ})
    (hd : (propDerivationSystem Axioms).Deriv L ψ) :
    ∃ L' : List (PL.Proposition Atom),
      (∀ x ∈ L', x ∈ S) ∧
      (propDerivationSystem Axioms).Deriv L' (φ → ψ) := by
  obtain ⟨d⟩ := hd
  -- Weaken to φ :: L, then DT gives L ⊢ φ → ψ
  have d_ext := DerivationTree.weakening L (φ :: L) ψ d
    (fun x hx => List.mem_cons.mpr (Or.inr hx))
  have d_dt := deductionTheorem h_implyK h_implyS L φ ψ d_ext
  by_cases hφL : φ ∈ L
  · -- φ ∈ L: use deductionWithMem to remove ALL occurrences of φ
    have d_mem := deductionWithMem h_implyK h_implyS L φ (φ → ψ) d_dt hφL
    -- d_mem : DerivationTree (removeAll L φ) (φ → (φ → ψ))
    -- removeAll L φ ⊆ S
    have h_rem_sub : ∀ x ∈ removeAll L φ, x ∈ S := by
      intro x hx
      simp only [removeAll, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not] at hx
      obtain ⟨hx_in, hx_ne⟩ := hx
      rcases hL x hx_in with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hx_ne
    -- Collapse φ → (φ → ψ) to φ → ψ via S-combinator + identity
    let ctx := removeAll L φ
    have d_is : DerivationTree Axioms (Atom := Atom) ctx
        ((φ.imp (φ.imp ψ)).imp ((φ.imp φ).imp (φ.imp ψ))) :=
      .weakening [] ctx _ (.ax [] _ (h_implyS φ φ ψ)) (fun _ h => nomatch h)
    -- MP: ctx ⊢ (φ → φ) → (φ → ψ)
    have d_step1 := DerivationTree.modus_ponens ctx _ _ d_is d_mem
    -- Build identity ⊢ φ → φ
    have d_k1 : DerivationTree Axioms (Atom := Atom) [] (φ.imp ((φ.imp φ).imp φ)) :=
      .ax [] _ (h_implyK φ (φ.imp φ))
    have d_s1 : DerivationTree Axioms (Atom := Atom) []
        ((φ.imp ((φ.imp φ).imp φ)).imp ((φ.imp (φ.imp φ)).imp (φ.imp φ))) :=
      .ax [] _ (h_implyS φ (φ.imp φ) φ)
    have d_mp1 := DerivationTree.modus_ponens [] _ _ d_s1 d_k1
    have d_k2 : DerivationTree Axioms (Atom := Atom) [] (φ.imp (φ.imp φ)) :=
      .ax [] _ (h_implyK φ φ)
    have d_id := DerivationTree.modus_ponens [] _ _ d_mp1 d_k2
    have d_id_w := DerivationTree.weakening [] ctx _ d_id (fun _ h => nomatch h)
    -- MP: ctx ⊢ φ → ψ
    have d_final := DerivationTree.modus_ponens ctx _ _ d_step1 d_id_w
    exact ⟨ctx, h_rem_sub, ⟨d_final⟩⟩
  · -- φ ∉ L: L ⊆ S already
    have hL_S : ∀ x ∈ L, x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hx) hφL
    exact ⟨L, hL_S, ⟨d_dt⟩⟩

/-! ## Closure Properties -/

/-- `S ⊆ GenericDeductiveClosure Axioms S`. -/
theorem generic_subset_deductive_closure
    (Axioms : PL.Proposition Atom → Prop)
    (S : Set (PL.Proposition Atom)) :
    S ⊆ GenericDeductiveClosure Axioms S :=
  fun φ hφ => ⟨[φ],
    fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ hφ,
    (propDerivationSystem Axioms).assumption (List.mem_cons.mpr (Or.inl rfl))⟩

/-- The generic deductive closure is deductively closed under `Axioms`. -/
theorem genericDeductiveClosure_closed
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (PL.Proposition Atom)}
    (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
    (hL : ∀ x ∈ L, x ∈ GenericDeductiveClosure Axioms S)
    (hd : (propDerivationSystem Axioms).Deriv L φ) :
    φ ∈ GenericDeductiveClosure Axioms S :=
  generic_deriv_from_closure_to_S h_implyK h_implyS L (fun x hx => hL x hx) φ hd

/-- Given a proof that `Cons` holds on the generic deductive closure of `S`,
`GenericDeductiveClosure Axioms S` is a `GenericTheory Axioms Cons`. -/
theorem genericDeductiveClosure_is_theory
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Cons : Set (PL.Proposition Atom) → Prop}
    {S : Set (PL.Proposition Atom)}
    (h_cons_cl : Cons (GenericDeductiveClosure Axioms S)) :
    GenericTheory Axioms Cons (GenericDeductiveClosure Axioms S) :=
  ⟨h_cons_cl,
   fun L φ hL hd => genericDeductiveClosure_closed h_implyK h_implyS L φ hL hd⟩

/-! ## Implication Witness Lemma (Generic) -/

/-- **Generic Implication Witness Lemma**: if `S` is a `GenericTheory Axioms Cons`
and `φ → ψ ∉ S`, and if the consistency predicate is preserved by extending `S`
with `φ` and taking the deductive closure (hypothesis `h_cons_ext`), then there
exists a `GenericTheory` `T ⊇ S` with `φ ∈ T` and `ψ ∉ T`.

The hypothesis `h_cons_ext` captures the explosion/EFQ property:
- **Minimal logic** (`Cons = fun _ => True`):
  `h_cons_ext = fun _ _ => trivial` (trivially vacuous).
- **Intuitionistic logic** (`Cons = PropSetConsistent IntPropAxiom`):
  `h_cons_ext` uses EFQ to prove `PropSetConsistent` of the closure of `S ∪ {φ}`.

See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43. -/
theorem generic_imp_witness
    {Axioms : PL.Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Cons : Set (PL.Proposition Atom) → Prop}
    {S : Set (PL.Proposition Atom)}
    (h_theory : GenericTheory Axioms Cons S)
    {φ ψ : PL.Proposition Atom}
    (h_cons_ext : GenericTheory Axioms Cons S → (φ → ψ) ∉ S →
      Cons (GenericDeductiveClosure Axioms (S ∪ {φ})))
    (h_not : (φ → ψ) ∉ S) :
    ∃ T : Set (PL.Proposition Atom),
      S ⊆ T ∧ GenericTheory Axioms Cons T ∧ φ ∈ T ∧ ψ ∉ T := by
  -- Obtain Cons on the closure of S ∪ {φ} via the explosion/EFQ witness
  have h_cons_cl : Cons (GenericDeductiveClosure Axioms (S ∪ {φ})) :=
    h_cons_ext h_theory h_not
  -- T is the generic deductive closure of S ∪ {φ}
  refine ⟨GenericDeductiveClosure Axioms (S ∪ {φ}), ?_, ?_, ?_, ?_⟩
  · -- S ⊆ T
    exact Set.Subset.trans Set.subset_union_left (generic_subset_deductive_closure _ _)
  · -- GenericTheory T
    exact genericDeductiveClosure_is_theory h_implyK h_implyS h_cons_cl
  · -- φ ∈ T
    exact generic_subset_deductive_closure _ _
      (Set.mem_union_right S (Set.mem_singleton_iff.mpr rfl))
  · -- ψ ∉ T
    intro ⟨L, hL_sub, hL_deriv⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ := generic_deriv_imp_of_union h_implyK h_implyS hL_sub hL_deriv
    exact h_not (h_theory.2 L' _ hL'_sub hL'_deriv)

end Cslib.Logic.PL
