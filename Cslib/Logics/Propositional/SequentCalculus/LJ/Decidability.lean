/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.Completeness
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.DecisionProcedure

/-! # Decidability of Intuitionistic Propositional Logic via LJ

This module proves that LJ derivability of sequents `Γ ⊢ A` is decidable for finite contexts
`Γ` of propositions over a decidable, hashable atom type.

## Strategy

The proof uses the **deduction theorem** for LJ together with the existing tableau-based
decidability of `IValid`. Concretely:

1. Define `listToImp` to encode a list of propositions as a prefix of implications:
   `listToImp [A₁, ..., Aₙ] C` is the proposition `A₁ → A₂ → ... → Aₙ → C`.

2. Define `ctxToImp` to encode a finite context as nested implications by converting
   to a list: `ctxToImp Γ A = listToImp Γ.toList A`.

3. Prove the **deduction equivalence**:
   `Nonempty (LJProof (Γ ⊢ A)) ↔ Nonempty (LJProof (∅ ⊢ ctxToImp Γ A))`
   using iterated `impR` / `impL` steps in each direction.

4. Combine with `lj_iff_ivalid` to reduce to `IValid (ctxToImp Γ A)`, which is decidable
   via `instDecidableIValid` from the intuitionistic tableau (routed through
   `ivalid_universe_invariant` to bridge `instDecidableIValid`'s `Type 0` pin to the unpinned
   universe `lj_iff_ivalid` needs).

## Main Results

- `listToImp`: List-to-implication encoding.
- `ctxToImp`: Context-to-implication encoding.
- `ljListDeductionFwd`: Forward deduction lemma for lists (list → implication chain).
- `ljListDeductionBwd`: Backward deduction lemma for lists (implication chain → context proof).
- `ljProofDeductionFwd`: Forward direction of the LJ deduction theorem.
- `ljProofDeductionBwd`: Backward direction of the LJ deduction theorem.
- `instDecidableLJDerivable`: `Decidable (Nonempty (LJProof (Γ ⊢ A)))`.
- `instDecidableDerivableInIPL`:
  `Decidable (DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A))`.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition InferenceSystem

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-! ## Context-to-Implication Encoding -/

/-- Encode a list of propositions as a prefix of implications.

`listToImp [A₁, A₂, ..., Aₙ] C` is the proposition `A₁ → A₂ → ... → Aₙ → C`.
This encodes the deduction theorem: a proof of `{A₁, ..., Aₙ} ⊢ C` corresponds
to a proof of `∅ ⊢ A₁ → A₂ → ... → Aₙ → C`. -/
def listToImp : List (Proposition Atom) → Proposition Atom → Proposition Atom
  | [], C => C
  | A :: As, C => A.imp (listToImp As C)

/-- Encode a finite context set as a prefix of implications.

`ctxToImp Γ A` is the proposition `A₁ → A₂ → ... → Aₙ → A` where `[A₁, ..., Aₙ] = Γ.toList`.
Used in the deduction theorem reduction for the decidability proof.

This is `noncomputable` because `Finset.toList` is `noncomputable`. -/
noncomputable def ctxToImp (Γ : Ctx Atom) (A : Proposition Atom) : Proposition Atom :=
  listToImp Γ.toList A

/-! ## Deduction Theorem: Forward Direction -/

/-- Forward deduction lemma for lists.

Given a proof of `(L.toFinset ∪ Γ) ⊢ C`, produce a proof of `Γ ⊢ listToImp L C`
by repeatedly discharging context elements as implications via `impR`. -/
def ljListDeductionFwd : ∀ (L : List (Proposition Atom)) (Γ : Ctx Atom) (C : Proposition Atom),
    LJProof ((L.toFinset ∪ Γ) ⊢ C) → LJProof (Γ ⊢ listToImp L C)
  | [], Γ, C, d => by
    simp only [listToImp]
    simpa using d
  | A :: As, Γ, C, d => by
    simp only [listToImp]
    apply SeqProof.impR A (listToImp As C)
    apply ljListDeductionFwd As (insert A Γ) C
    apply LJProof.mono _ d
    intro x hx
    simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
      List.mem_toFinset] at hx ⊢
    tauto

/-- Forward direction of the deduction theorem for LJ.

A proof of `Γ ⊢ A` gives a proof of `∅ ⊢ ctxToImp Γ A` by repeatedly introducing
implications via `impR` to discharge all context assumptions.

This is `noncomputable` because `ctxToImp` uses `Finset.toList`. -/
noncomputable def ljProofDeductionFwd {Γ : Ctx Atom} {A : Proposition Atom}
    (d : LJProof (Γ ⊢ A)) : LJProof (∅ ⊢ ctxToImp Γ A) := by
  unfold ctxToImp
  apply ljListDeductionFwd Γ.toList ∅ A
  simp only [Finset.toList_toFinset, Finset.union_empty]
  exact d

/-! ## Deduction Theorem: Backward Direction -/

/-- Backward deduction lemma for lists.

Given a proof of `Γ ⊢ listToImp L C`, produce a proof of `(L.toFinset ∪ Γ) ⊢ C`.

The proof works by induction on `L`. For each head `A`:
- Weaken the proof `d : LJProof (Γ ⊢ A → listToImp As C)` to the larger context `Γ'`.
- Use `cut` (via `impL` after weakening) to derive `Γ' ⊢ listToImp As C`.
- Apply the induction hypothesis to continue peeling off implications.
- Conclude by `mono` (since `Γ' ⊆ As.toFinset ∪ Γ'`). -/
def ljListDeductionBwd : ∀ (L : List (Proposition Atom)) (Γ : Ctx Atom) (C : Proposition Atom),
    LJProof (Γ ⊢ listToImp L C) → LJProof ((L.toFinset ∪ Γ) ⊢ C)
  | [], Γ, C, d => by
    simp only [List.toFinset_nil, Finset.empty_union]
    exact d
  | A :: As, Γ, C, d => by
    simp only [listToImp] at d
    -- d : LJProof (Γ ⊢ A.imp (listToImp As C))
    -- Goal: LJProof ((insert A As.toFinset ∪ Γ) ⊢ C)
    -- Context we're working in: Γ' = insert A As.toFinset ∪ Γ
    -- (1) Weaken d to Γ': Γ' ⊢ A → listToImp As C
    have d' : LJProof ((List.toFinset (A :: As) ∪ Γ) ⊢ A.imp (listToImp As C)) :=
      LJProof.mono (Finset.subset_union_right) d
    -- (2) A is in Γ'
    have hA : A ∈ (List.toFinset (A :: As) ∪ Γ) := by
      simp [List.toFinset_cons]
    -- (3) Use cut on (A → listToImp As C): get Γ' ⊢ listToImp As C
    --     cut (A → rest) d' (impL A rest mem_imp ax_A ax_rest)
    --     where mem_imp comes from the cut inserting (A → rest) into context
    have dRest : LJProof ((List.toFinset (A :: As) ∪ Γ) ⊢ listToImp As C) :=
      SeqProof.cut (A.imp (listToImp As C)) d' (
        SeqProof.impL A (listToImp As C)
          (Finset.mem_insert_self _ _)
          (SeqProof.ax A _ (Finset.mem_insert_of_mem hA))
          (SeqProof.ax _ _ (Finset.mem_insert_self _ _)))
    -- (4) Apply IH to dRest to get (As.toFinset ∪ Γ' ⊢ C)
    have dIH := ljListDeductionBwd As (List.toFinset (A :: As) ∪ Γ) C dRest
    -- (5) The two contexts are equal by set arithmetic:
    --     As.toFinset ∪ ((A :: As).toFinset ∪ Γ) = (A :: As).toFinset ∪ Γ
    have heq : As.toFinset ∪ ((A :: As).toFinset ∪ Γ) = (A :: As).toFinset ∪ Γ := by
      ext x; simp [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    rw [heq] at dIH
    exact dIH

/-- Backward direction of the deduction theorem for LJ.

A proof of `∅ ⊢ ctxToImp Γ A` gives a proof of `Γ ⊢ A` by repeatedly eliminating
implications from the antecedent using `impL` steps.

This is `noncomputable` because `ctxToImp` uses `Finset.toList`. -/
noncomputable def ljProofDeductionBwd {Γ : Ctx Atom} {A : Proposition Atom}
    (d : LJProof (∅ ⊢ ctxToImp Γ A)) : LJProof (Γ ⊢ A) := by
  unfold ctxToImp at d
  have h := ljListDeductionBwd Γ.toList ∅ A d
  simp only [Finset.toList_toFinset, Finset.union_empty] at h
  exact h

/-! ## Decidability Instances -/

/-- `Nonempty (LJProof (Γ ⊢ A))` is decidable for finite contexts over decidable, hashable atoms.

The proof reduces LJ derivability to intuitionistic validity via the deduction theorem
and `lj_iff_ivalid`:
1. `Nonempty (LJProof (Γ ⊢ A)) ↔ Nonempty (LJProof (∅ ⊢ ctxToImp Γ A))` by the
   deduction theorem (`ljProofDeductionFwd` and `ljProofDeductionBwd`).
2. `Nonempty (LJProof (∅ ⊢ ctxToImp Γ A)) ↔ IValid (ctxToImp Γ A)` by `lj_iff_ivalid`.
3. `IValid (ctxToImp Γ A)` is decidable by `instDecidableIValid` (from the intuitionistic
   tableau decision procedure).

The instance is `noncomputable` because `ctxToImp` uses `Finset.toList`.

**Universe note.** `instDecidableIValid` (from `Intuitionistic/DecisionProcedure.lean`) is pinned
to `IValid.{_, 0}`, while `lj_iff_ivalid` needs `IValid.{u, u}` (`u` = `Atom`'s own universe). The
local `letI` below routes through `ivalid_universe_invariant` -- the same bridge
`instDecidableDerivableIntPropAxiom` uses -- to recover an unpinned `Decidable (IValid _)`
instance before `decidable_of_iff` is applied, exactly mirroring
`Minimal/DecisionProcedure.lean`'s `mvalid_universe_invariant` pattern. -/
noncomputable instance instDecidableLJDerivable {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (Nonempty (LJProof (Γ ⊢ A))) :=
  letI : Decidable (IValid (ctxToImp Γ A)) :=
    decidable_of_iff (IValid.{_, 0} (ctxToImp Γ A))
      (ivalid_universe_invariant (ctxToImp Γ A)).symm
  decidable_of_iff (IValid (ctxToImp Γ A)) <| by
    constructor
    · -- IValid (ctxToImp Γ A) → Nonempty (LJProof (Γ ⊢ A))
      intro hv
      -- lj_iff_ivalid.mp : IValid φ → Nonempty (LJProof (∅ ⊢ φ))
      obtain ⟨d⟩ := lj_iff_ivalid.mp hv
      exact ⟨ljProofDeductionBwd d⟩
    · -- Nonempty (LJProof (Γ ⊢ A)) → IValid (ctxToImp Γ A)
      intro ⟨d⟩
      -- lj_iff_ivalid.mpr : Nonempty (LJProof (∅ ⊢ φ)) → IValid φ
      exact lj_iff_ivalid.mpr ⟨ljProofDeductionFwd d⟩

/-- `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A)` is decidable for finite contexts
over decidable, hashable atoms.

Obtained by combining `instDecidableLJDerivable` with the ND–LJ bridge `nd_iff_lj`. -/
noncomputable instance instDecidableDerivableInIPL {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) (Γ ⊢ A)) :=
  decidable_of_iff (Nonempty (LJProof (Γ ⊢ A))) nd_iff_lj.symm

end Cslib.Logic.PL

end
