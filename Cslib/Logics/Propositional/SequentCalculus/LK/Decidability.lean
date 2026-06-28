/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LK.Completeness
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability
public import Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure

/-! # Decidability of Classical Propositional Logic via LK

This module proves that LK derivability of single-succedent sequents `Γ ⊢ₛ {A}` is
decidable for finite contexts `Γ` over a decidable, hashable atom type.

## Strategy

The proof mirrors `LJ/Decidability.lean`, using the deduction theorem for LK together
with the existing classical tautology decision procedure. Concretely:

1. Reuse `listToImp` and `ctxToImp` from `LJ.Decidability` to encode a context as a
   prefix of implications: `ctxToImp Γ A = A₁ → A₂ → ... → Aₙ → A`.

2. Prove the **deduction equivalence**:
   `Nonempty (LKProof (Γ ⊢ₛ {A})) ↔ Nonempty (LKProof (∅ ⊢ₛ {ctxToImp Γ A}))`
   using iterated `impR` / `impL` steps in each direction.

3. Combine with `lk_iff_tautology` to reduce to `Tautology (ctxToImp Γ A)`, which is
   decidable via `instDecidableTautologyTableau`.

## Main Results

- `lkListDeductionFwd`: Forward deduction lemma for lists.
- `lkListDeductionBwd`: Backward deduction lemma for lists.
- `lkProofDeductionFwd`: Forward direction of the LK deduction theorem.
- `lkProofDeductionBwd`: Backward direction of the LK deduction theorem.
- `instDecidableLKDerivable`: `Decidable (Nonempty (LKProof (Γ ⊢ₛ {A})))`.
- `instDecidableDerivableInCPL`:
  `Decidable (DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ A))`.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition LKSequent InferenceSystem

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-! ## Deduction Theorem: Forward Direction -/

/-- Forward deduction lemma for lists.

Given a proof of `(L.toFinset ∪ Γ) ⊢ₛ {C}`, produce a proof of `Γ ⊢ₛ {listToImp L C}`
by repeatedly discharging context elements as implications via `impR`. -/
def lkListDeductionFwd :
    ∀ (L : List (Proposition Atom)) (Γ : Ctx Atom) (C : Proposition Atom),
    LKProof ((L.toFinset ∪ Γ) ⊢ₛ {C}) → LKProof (Γ ⊢ₛ {listToImp L C})
  | [], Γ, C, d => by
    simp only [listToImp]
    simpa using d
  | A :: As, Γ, C, d => by
    simp only [listToImp]
    -- Apply impR to introduce A → listToImp As C.
    apply LKProof.impR A (listToImp As C) (Finset.mem_singleton.mpr rfl)
    -- After impR, goal: LKProof (insert A Γ ⊢ₛ insert (listToImp As C) {A → listToImp As C}).
    -- Get d_rec : LKProof (insert A Γ ⊢ₛ {listToImp As C}) from recursion, then weaken.
    apply (lkListDeductionFwd As (insert A Γ) C _).mono
      (Finset.Subset.refl _) (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
    -- Goal: LKProof ((As.toFinset ∪ insert A Γ) ⊢ₛ {C}).
    apply LKProof.mono _ (Finset.Subset.refl _) d
    intro x hx
    simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
      List.mem_toFinset] at hx ⊢
    tauto

/-- Forward direction of the deduction theorem for LK.

A proof of `Γ ⊢ₛ {A}` gives a proof of `∅ ⊢ₛ {ctxToImp Γ A}` by repeatedly introducing
implications via `impR` to discharge all context assumptions.

This is `noncomputable` because `ctxToImp` uses `Finset.toList`. -/
noncomputable def lkProofDeductionFwd {Γ : Ctx Atom} {A : Proposition Atom}
    (d : LKProof (Γ ⊢ₛ {A})) : LKProof (∅ ⊢ₛ {ctxToImp Γ A}) := by
  unfold ctxToImp
  apply lkListDeductionFwd Γ.toList ∅ A
  simp only [Finset.toList_toFinset, Finset.union_empty]
  exact d

/-! ## Deduction Theorem: Backward Direction -/

/-- Backward deduction lemma for lists.

Given a proof of `Γ ⊢ₛ {listToImp L C}`, produce a proof of `(L.toFinset ∪ Γ) ⊢ₛ {C}`.

The proof works by induction on `L`. For each head `A`:
- Weaken `d : LKProof (Γ ⊢ₛ {A → listToImp As C})` to the enlarged context `Γ'`.
- Use `cut` on `(A → rest)` to derive `Γ' ⊢ₛ {rest}` via `impL`.
- Apply the induction hypothesis to continue peeling off implications.
- Conclude by set arithmetic. -/
def lkListDeductionBwd :
    ∀ (L : List (Proposition Atom)) (Γ : Ctx Atom) (C : Proposition Atom),
    LKProof (Γ ⊢ₛ {listToImp L C}) → LKProof ((L.toFinset ∪ Γ) ⊢ₛ {C})
  | [], Γ, C, d => by
    simp only [List.toFinset_nil, Finset.empty_union]
    exact d
  | A :: As, Γ, C, d => by
    simp only [listToImp] at d
    -- d : LKProof (Γ ⊢ₛ {A → listToImp As C})
    -- Goal: LKProof ((insert A As.toFinset ∪ Γ) ⊢ₛ {C})
    -- Let Γ' = (A :: As).toFinset ∪ Γ.
    -- (1) Weaken d to Γ': Γ' ⊢ₛ {A → listToImp As C}
    have d' : LKProof ((List.toFinset (A :: As) ∪ Γ) ⊢ₛ {A.imp (listToImp As C)}) :=
      LKProof.mono Finset.subset_union_right (Finset.Subset.refl _) d
    -- (2) A ∈ Γ'
    have hA : A ∈ List.toFinset (A :: As) ∪ Γ := by
      simp [List.toFinset_cons]
    -- (3) Use cut on (A → rest) to derive Γ' ⊢ₛ {listToImp As C}.
    --     Left  premise: Γ' ⊢ₛ {A → rest, listToImp As C}  (from d' by weakR)
    --     Right premise: insert (A → rest) Γ' ⊢ₛ {listToImp As C}  (from impL)
    have dRest : LKProof ((List.toFinset (A :: As) ∪ Γ) ⊢ₛ {listToImp As C}) :=
      LKProof.cut (A.imp (listToImp As C))
        (LKProof.mono (Finset.Subset.refl _)
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) d')
        (LKProof.impL A (listToImp As C)
          (Finset.mem_insert_self _ _)
          (LKProof.ax A _ _ (Finset.mem_insert_of_mem hA) (Finset.mem_insert_self _ _))
          (LKProof.ax (listToImp As C) _ _ (Finset.mem_insert_self _ _)
            (Finset.mem_singleton.mpr rfl)))
    -- (4) Apply IH to dRest: (As.toFinset ∪ Γ') ⊢ₛ {C}
    have dIH := lkListDeductionBwd As (List.toFinset (A :: As) ∪ Γ) C dRest
    -- (5) Set arithmetic: As.toFinset ∪ ((A :: As).toFinset ∪ Γ) = (A :: As).toFinset ∪ Γ
    have heq : As.toFinset ∪ (List.toFinset (A :: As) ∪ Γ) = List.toFinset (A :: As) ∪ Γ := by
      ext x; simp [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    rw [heq] at dIH
    exact dIH

/-- Backward direction of the deduction theorem for LK.

A proof of `∅ ⊢ₛ {ctxToImp Γ A}` gives a proof of `Γ ⊢ₛ {A}` by repeatedly eliminating
implications from the antecedent using `impL` steps.

This is `noncomputable` because `ctxToImp` uses `Finset.toList`. -/
noncomputable def lkProofDeductionBwd {Γ : Ctx Atom} {A : Proposition Atom}
    (d : LKProof (∅ ⊢ₛ {ctxToImp Γ A})) : LKProof (Γ ⊢ₛ {A}) := by
  unfold ctxToImp at d
  have h := lkListDeductionBwd Γ.toList ∅ A d
  simp only [Finset.toList_toFinset, Finset.union_empty] at h
  exact h

/-! ## Decidability Instances -/

/-- `Nonempty (LKProof (Γ ⊢ₛ {A}))` is decidable for finite contexts over decidable,
hashable atoms.

The proof reduces LK derivability to classical tautology via the deduction theorem and
`lk_iff_tautology`:
1. `Nonempty (LKProof (Γ ⊢ₛ {A})) ↔ Nonempty (LKProof (∅ ⊢ₛ {ctxToImp Γ A}))` by the
   deduction theorem.
2. `Nonempty (LKProof (∅ ⊢ₛ {ctxToImp Γ A})) ↔ Tautology (ctxToImp Γ A)` by
   `lk_iff_tautology`.
3. `Tautology (ctxToImp Γ A)` is decidable by `instDecidableTautologyTableau`.

The instance is `noncomputable` because `ctxToImp` uses `Finset.toList`. -/
noncomputable instance instDecidableLKDerivable {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (Nonempty (LKProof (Γ ⊢ₛ {A}))) :=
  decidable_of_iff (Tautology (ctxToImp Γ A)) <| by
    constructor
    · -- Tautology (ctxToImp Γ A) → Nonempty (LKProof (Γ ⊢ₛ {A}))
      intro hv
      obtain ⟨d⟩ := lk_iff_tautology.mp hv
      exact ⟨lkProofDeductionBwd d⟩
    · -- Nonempty (LKProof (Γ ⊢ₛ {A})) → Tautology (ctxToImp Γ A)
      intro ⟨d⟩
      exact lk_iff_tautology.mpr ⟨lkProofDeductionFwd d⟩

/-- `DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ A)` is decidable for finite contexts
over decidable, hashable atoms.

Obtained by combining `instDecidableLKDerivable` with the ND–LK bridge `nd_iff_lk`. -/
noncomputable instance instDecidableDerivableInCPL {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom) (Γ ⊢ A)) :=
  decidable_of_iff (Nonempty (LKProof (Γ ⊢ₛ {A}))) nd_iff_lk.symm

end Cslib.Logic.PL

end
