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
   to a list: `ctxToImp Γ A = listToImp Γ.toList A`. This is used only in the *statements* of
   the deduction-theorem lemmas (`ljProofDeductionFwd`/`ljProofDeductionBwd`); it stays
   `noncomputable`, inherently so, since no computable choice of list representative for a
   `Finset` exists in general.

3. Prove the **deduction equivalence**:
   `Nonempty (LJProof (Γ ⊢ A)) ↔ Nonempty (LJProof (∅ ⊢ ctxToImp Γ A))`
   using iterated `impR` / `impL` steps in each direction.

4. Combine with `lj_iff_ivalid` to reduce to `IValid (ctxToImp Γ A)`, which is decidable
   via `instDecidableIValid` from the intuitionistic tableau (routed through
   `ivalid_universe_invariant` to bridge `instDecidableIValid`'s `Type 0` pin to the unpinned
   universe `lj_iff_ivalid` needs).

5. Make the resulting `Decidable` **instance** computable by sidestepping `ctxToImp` at the
   instance level: `ljListDerivableDecidable` proves the same equivalence at the *list* level
   (computable, since `listToImp` needs no representative choice), and
   `instDecidableLJDerivable` eliminates `Γ`'s underlying `Multiset` into it via
   `Quotient.recOnSubsingleton`, choosing an arbitrary list representative. Since `Decidable p`
   is a `Subsingleton`, the resulting *decision* is representative-independent even though the
   intermediate `listToImp` formula is not.

## Main Results

- `listToImp`: List-to-implication encoding.
- `ctxToImp`: Context-to-implication encoding (statement-level only; inherently noncomputable).
- `ljListDeductionFwd`: Forward deduction lemma for lists (list → implication chain).
- `ljListDeductionBwd`: Backward deduction lemma for lists (implication chain → context proof).
- `ljProofDeductionFwd`: Forward direction of the LJ deduction theorem.
- `ljProofDeductionBwd`: Backward direction of the LJ deduction theorem.
- `ljListDerivableDecidable`: List-level decidability helper, computable, used to build
  `instDecidableLJDerivable` via `Quotient.recOnSubsingleton`.
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

This is `noncomputable` **inherently**, not incidentally: a computable function out of
`Finset` must be invariant under permutation of the underlying list, but `listToImp` is not
(`A → B → C` and `B → A → C` are distinct `Proposition Atom` values), so no computable
`Ctx Atom → Proposition Atom → Proposition Atom` extending `listToImp` exists. This no longer
affects any decision procedure: `instDecidableLJDerivable` below sidesteps `ctxToImp` entirely
via `ljListDerivableDecidable` and `Quotient.recOnSubsingleton`. -/
noncomputable def ctxToImp (Γ : Ctx Atom) (A : Proposition Atom) : Proposition Atom :=
  listToImp Γ.toList A

/-! ## Deduction Theorem: Forward Direction -/

/-- Forward deduction lemma for lists, generic over the theory `T`.

Given a proof of `(L.toFinset ∪ Γ) ⊢ C`, produce a proof of `Γ ⊢ listToImp L C`
by repeatedly discharging context elements as implications via `impR`. Every rule used here
(`impR`, `mono`) is in the ungated ten-rule minimal base of `SeqProof`; none touches the gated
`botL`, so this generalises from `LJProof` (`= SeqProof IPL`) to `SeqProof T` for an arbitrary
`T` with no proof change beyond the binder. -/
def seqListDeductionFwd {T : Theory Atom} :
    ∀ (L : List (Proposition Atom)) (Γ : Ctx Atom) (C : Proposition Atom),
    SeqProof T ((L.toFinset ∪ Γ) ⊢ C) → SeqProof T (Γ ⊢ listToImp L C)
  | [], Γ, C, d => by
    simp only [listToImp]
    simpa using d
  | A :: As, Γ, C, d => by
    simp only [listToImp]
    apply SeqProof.impR A (listToImp As C)
    apply seqListDeductionFwd As (insert A Γ) C
    apply SeqProof.mono d
    intro x hx
    simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
      List.mem_toFinset] at hx ⊢
    tauto

/-- Forward direction of the deduction theorem, generic over the theory `T`.

A proof of `Γ ⊢ A` gives a proof of `∅ ⊢ ctxToImp Γ A` by repeatedly introducing
implications via `impR` to discharge all context assumptions.

This is `noncomputable` because it is stated in terms of `ctxToImp`, whose noncomputability
is inherent (see `ctxToImp`'s docstring) rather than a defect. No decision procedure depends on
this declaration. -/
noncomputable def seqProofDeductionFwd {T : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (d : SeqProof T (Γ ⊢ A)) : SeqProof T (∅ ⊢ ctxToImp Γ A) := by
  unfold ctxToImp
  apply seqListDeductionFwd Γ.toList ∅ A
  simp only [Finset.toList_toFinset, Finset.union_empty]
  exact d

/-! ## Deduction Theorem: Backward Direction -/

/-- Backward deduction lemma for lists, generic over the theory `T`.

Given a proof of `Γ ⊢ listToImp L C`, produce a proof of `(L.toFinset ∪ Γ) ⊢ C`.

The proof works by induction on `L`. For each head `A`:
- Weaken the proof `d : SeqProof T (Γ ⊢ A → listToImp As C)` to the larger context `Γ'`.
- Use `cut` (via `impL` after weakening) to derive `Γ' ⊢ listToImp As C`.
- Apply the induction hypothesis to continue peeling off implications.
- Conclude by `mono` (since `Γ' ⊆ As.toFinset ∪ Γ'`).

Every rule used here (`ax`, `impL`, `cut`, `mono`) is in the ungated ten-rule minimal base of
`SeqProof`; none touches the gated `botL`. -/
def seqListDeductionBwd {T : Theory Atom} :
    ∀ (L : List (Proposition Atom)) (Γ : Ctx Atom) (C : Proposition Atom),
    SeqProof T (Γ ⊢ listToImp L C) → SeqProof T ((L.toFinset ∪ Γ) ⊢ C)
  | [], Γ, C, d => by
    simp only [List.toFinset_nil, Finset.empty_union]
    exact d
  | A :: As, Γ, C, d => by
    simp only [listToImp] at d
    -- d : SeqProof T (Γ ⊢ A.imp (listToImp As C))
    -- Goal: SeqProof T ((insert A As.toFinset ∪ Γ) ⊢ C)
    -- Context we're working in: Γ' = insert A As.toFinset ∪ Γ
    -- (1) Weaken d to Γ': Γ' ⊢ A → listToImp As C
    have d' : SeqProof T ((List.toFinset (A :: As) ∪ Γ) ⊢ A.imp (listToImp As C)) :=
      SeqProof.mono d Finset.subset_union_right
    -- (2) A is in Γ'
    have hA : A ∈ (List.toFinset (A :: As) ∪ Γ) := by
      simp [List.toFinset_cons]
    -- (3) Use cut on (A → listToImp As C): get Γ' ⊢ listToImp As C
    --     cut (A → rest) d' (impL A rest mem_imp ax_A ax_rest)
    --     where mem_imp comes from the cut inserting (A → rest) into context
    have dRest : SeqProof T ((List.toFinset (A :: As) ∪ Γ) ⊢ listToImp As C) :=
      SeqProof.cut (A.imp (listToImp As C)) d' (
        SeqProof.impL A (listToImp As C)
          (Finset.mem_insert_self _ _)
          (SeqProof.ax A _ (Finset.mem_insert_of_mem hA))
          (SeqProof.ax _ _ (Finset.mem_insert_self _ _)))
    -- (4) Apply IH to dRest to get (As.toFinset ∪ Γ' ⊢ C)
    have dIH := seqListDeductionBwd As (List.toFinset (A :: As) ∪ Γ) C dRest
    -- (5) The two contexts are equal by set arithmetic:
    --     As.toFinset ∪ ((A :: As).toFinset ∪ Γ) = (A :: As).toFinset ∪ Γ
    have heq : As.toFinset ∪ ((A :: As).toFinset ∪ Γ) = (A :: As).toFinset ∪ Γ := by
      ext x; simp [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    rw [heq] at dIH
    exact dIH

/-- Backward direction of the deduction theorem, generic over the theory `T`.

A proof of `∅ ⊢ ctxToImp Γ A` gives a proof of `Γ ⊢ A` by repeatedly eliminating
implications from the antecedent using `impL` steps.

This is `noncomputable` because it is stated in terms of `ctxToImp`, whose noncomputability
is inherent (see `ctxToImp`'s docstring) rather than a defect. No decision procedure depends on
this declaration. -/
noncomputable def seqProofDeductionBwd {T : Theory Atom} {Γ : Ctx Atom} {A : Proposition Atom}
    (d : SeqProof T (∅ ⊢ ctxToImp Γ A)) : SeqProof T (Γ ⊢ A) := by
  unfold ctxToImp at d
  have h := seqListDeductionBwd Γ.toList ∅ A d
  simp only [Finset.toList_toFinset, Finset.union_empty] at h
  exact h

/-! ## Deduction Theorem: IPL Re-Exports -/

/-- Forward deduction lemma for lists, re-exported at `IPL` from `seqListDeductionFwd`.
Preserves the pre-generalisation name and signature for `LJProof` call sites. -/
@[reducible] def ljListDeductionFwd (L : List (Proposition Atom)) (Γ : Ctx Atom)
    (C : Proposition Atom) (d : LJProof ((L.toFinset ∪ Γ) ⊢ C)) :
    LJProof (Γ ⊢ listToImp L C) :=
  seqListDeductionFwd L Γ C d

/-- Forward direction of the deduction theorem for LJ, re-exported at `IPL` from
`seqProofDeductionFwd`. Preserves the pre-generalisation name and signature. -/
noncomputable def ljProofDeductionFwd {Γ : Ctx Atom} {A : Proposition Atom}
    (d : LJProof (Γ ⊢ A)) : LJProof (∅ ⊢ ctxToImp Γ A) :=
  seqProofDeductionFwd d

/-- Backward deduction lemma for lists, re-exported at `IPL` from `seqListDeductionBwd`.
Preserves the pre-generalisation name and signature for `LJProof` call sites. -/
@[reducible] def ljListDeductionBwd (L : List (Proposition Atom)) (Γ : Ctx Atom)
    (C : Proposition Atom) (d : LJProof (Γ ⊢ listToImp L C)) :
    LJProof ((L.toFinset ∪ Γ) ⊢ C) :=
  seqListDeductionBwd L Γ C d

/-- Backward direction of the deduction theorem for LJ, re-exported at `IPL` from
`seqProofDeductionBwd`. Preserves the pre-generalisation name and signature. -/
noncomputable def ljProofDeductionBwd {Γ : Ctx Atom} {A : Proposition Atom}
    (d : LJProof (∅ ⊢ ctxToImp Γ A)) : LJProof (Γ ⊢ A) :=
  seqProofDeductionBwd d

/-! ## Decidability Instances -/

/-- List-level decidability of LJ derivability from a `Nodup` list context.

Given a `Nodup` list `l` and the proof `h` that its coercion to a `Multiset` is `Nodup`, decides
`Nonempty (LJProof ((⟨↑l, h⟩ : Finset (Proposition Atom)) ⊢ A))` by routing through
`IValid (listToImp l A)`, exactly as `instDecidableLJDerivable` used to route through
`IValid (ctxToImp Γ A)` -- but `listToImp` applied to a concrete list needs no choice of
representative, so this helper is computable. `instDecidableLJDerivable` builds on this helper
via `Quotient.recOnSubsingleton`, applying it to an arbitrary representative of `Γ`'s underlying
`Multiset`; the resulting *decision* is representative-independent because `Decidable p` is a
`Subsingleton`, even though `listToImp l A` itself is not invariant under permuting `l`.

**Universe note.** `instDecidableIValid` (from `Intuitionistic/DecisionProcedure.lean`) is pinned
to `IValid.{_, 0}`, while `lj_iff_ivalid` needs `IValid.{u, u}` (`u` = `Atom`'s own universe). The
local `letI` below routes through `ivalid_universe_invariant` -- the same bridge
`instDecidableDerivableIntPropAxiom` uses -- to recover an unpinned `Decidable (IValid _)`
instance before `decidable_of_iff` is applied, exactly mirroring
`Minimal/DecisionProcedure.lean`'s `mvalid_universe_invariant` pattern. -/
def ljListDerivableDecidable (l : List (Proposition Atom))
    (h : (↑l : Multiset (Proposition Atom)).Nodup) (A : Proposition Atom) :
    Decidable (Nonempty (LJProof ((⟨↑l, h⟩ : Finset (Proposition Atom)) ⊢ A))) :=
  letI : Decidable (IValid (listToImp l A)) :=
    decidable_of_iff (IValid.{_, 0} (listToImp l A)) (ivalid_universe_invariant _).symm
  decidable_of_iff (IValid (listToImp l A)) <| by
    have hset : (⟨(↑l : Multiset (Proposition Atom)), h⟩ : Finset (Proposition Atom))
        = l.toFinset := List.toFinset_eq h
    rw [hset]
    constructor
    · -- IValid (listToImp l A) → Nonempty (LJProof (l.toFinset ⊢ A))
      intro hv
      obtain ⟨d⟩ := lj_iff_ivalid.mp hv
      have hd := ljListDeductionBwd l ∅ A d
      rw [Finset.union_empty] at hd
      exact ⟨hd⟩
    · -- Nonempty (LJProof (l.toFinset ⊢ A)) → IValid (listToImp l A)
      rintro ⟨d⟩
      refine lj_iff_ivalid.mpr ⟨ljListDeductionFwd l ∅ A ?_⟩
      rw [Finset.union_empty]
      exact d

/-- `Nonempty (LJProof (Γ ⊢ A))` is decidable for finite contexts over decidable, hashable atoms.

The instance eliminates `Γ`'s underlying `Multiset` via `Quotient.recOnSubsingleton` into
`ljListDerivableDecidable`, applied to an arbitrary list representative `l` of `Γ.val` with
`Γ.nodup` as the `Nodup` witness. Since `Decidable p` is a `Subsingleton`, the elimination is
sound -- the resulting decision does not depend on which representative is chosen -- and, because
`ljListDerivableDecidable` is itself computable, so is this instance. The reconstruction
`⟨Γ.val, Γ.nodup⟩` is definitionally `Γ` by structure eta, so no cast is needed at this level. -/
instance instDecidableLJDerivable {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (Nonempty (LJProof (Γ ⊢ A))) :=
  Quotient.recOnSubsingleton (motive := fun (s : Multiset (Proposition Atom)) =>
      (h : s.Nodup) → Decidable (Nonempty (LJProof ((⟨s, h⟩ : Finset (Proposition Atom)) ⊢ A))))
    Γ.val (fun l h => ljListDerivableDecidable l h A) Γ.nodup

/-- `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A)` is decidable for finite contexts
over decidable, hashable atoms.

Obtained by combining `instDecidableLJDerivable` with the ND–LJ bridge `nd_iff_lj`. -/
instance instDecidableDerivableInIPL {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) (Γ ⊢ A)) :=
  decidable_of_iff (Nonempty (LJProof (Γ ⊢ A))) nd_iff_lj.symm

end Cslib.Logic.PL

end
