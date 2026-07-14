/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.Segment

/-! # Segment Lindenbaum Lemmas for Constructive Modal Logic

This module provides the saturation/realization layer for the `CK` canonical segment model:
quasi-prime extension (Lindenbaum at the trivially-true consistency predicate) and the three
*refuting-theory* lemmas consumed by the backward truth-lemma cases (`CKTruthLemma.lean`).

**For `CK`/`CT`/`CS4`, the plan's feared "two-level tail-assembly fixpoint" does not arise**:
following ianshil/CK `general_seg_completeness.v`, tails are set comprehensions
(`CKSegment.ofHead`'s maximal tail, and the diamond-refuting restricted tail built in
`CKTruthLemma.lean`), so the only constructions needed here are *single-theory* prime extensions
plus the boxed-context transfer lemma (`box_mem_of_boxed_context`, the `K`-rule analogue for
deductively closed sets).

**This is false for `CS5`** (task 509): the symmetric tail's truth-lemma box-backward case can
require enlarging a head `H` to `H' ⊇ H` and its tail `T` *simultaneously* — enlarging `H'`
enlarges `boxInv H'` in turn, so `H'` and `T` cannot be built as two sequential single-theory
extensions (`cs5_symmetric_tail_box_gap`,
`Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean`, mechanizes why the sequential route fails).
`CS5`'s box-backward case therefore needs a genuine simultaneous-pair construction, the one
two-level fixpoint this module's single-theory lemmas do not by themselves supply — see
`CS5.lean`'s module docstring for the current status.

## Main Results

- `quasi_prime_exclusion`: Lindenbaum for quasi-prime theories — any deductively closed set
  omitting `φ` extends to a quasi-prime theory omitting `φ`. `Metalogic.prime_exclusion` at
  `Cons := fun _ => True` (the trivially-true predicate admits the exploding theory, so no
  consistency side conditions arise).
- `box_mem_of_boxed_context`: if `L ⊢ φ` and `□ψ ∈ H` for every `ψ ∈ L`, then `□φ ∈ H`
  (for `H` deductively closed) — by iterated deduction, necessitation, and `Kb`.
- `imp_refuting_theory`: if `φ → ψ ∉ H`, some quasi-prime `T ⊇ H ∪ {φ}` omits `ψ`.
- `box_refuting_theory`: if `□A ∉ H`, some quasi-prime `T ⊇ boxInv H` omits `A`.
- `dia_refuting_theory`: if `◇B ∈ H` and `◇A ∉ H`, some quasi-prime `T ⊇ boxInv H ∪ {B}`
  omits `A` (uses `Kd` — the only place the diamond axiom enters the construction).
- `segment_realization`: any `CK`-underivable formula is omitted by the head of some
  segment.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5.
* ianshil/CK `Completeness_seg/general_seg_completeness.v` — the reference mechanization.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Quasi-Prime Lindenbaum -/

/-- **Quasi-prime exclusion** (Lindenbaum at the trivially-true consistency predicate):
any deductively closed `S` with `phi ∉ S` extends to a quasi-prime `T ⊇ S` with `phi ∉ T`.

Thin wrapper around `Metalogic.prime_exclusion` with `Cons := fun _ => True`,
`cl := modalDeductiveClosure Axioms`. With the trivial `Cons`, the consistency-flavoured
hypotheses of `prime_exclusion` become vacuous or trivial: no `efq` bridge is needed, and
chains preserve `Cons` for free. The exploding theory is admissible, exactly as the segment
model requires. -/
theorem quasi_prime_exclusion
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    {S : Set (Proposition Atom)}
    (h_closed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) S)
    {phi : Proposition Atom} (h_not : phi ∉ S) :
    ∃ T, S ⊆ T ∧ QuasiPrime Axioms T ∧ phi ∉ T :=
  Metalogic.prime_exclusion
    (modalDerivationSystem Axioms) (fun _ => True)
    ⟨trivial, h_closed⟩ h_not
    (fun A B χ => ⟨.ax [] _ (h_orE A B χ)⟩)
    (modalDeductiveClosure Axioms)
    (modal_subset_deductive_closure Axioms)
    (fun {_X _ψ} h => h)
    (fun {_X} _ => ⟨trivial,
      fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd⟩)
    (fun {_X} h_not_cons => absurd trivial h_not_cons)
    (fun {U _L a _b} hL hd =>
      modal_deriv_imp_of_union h_implyK h_implyS
        (fun x hx => by
          rcases Set.mem_insert_iff.mp (hL x hx) with rfl | hu
          · exact Set.mem_union_right U (Set.mem_singleton_iff.mpr rfl)
          · exact Set.mem_union_left _ hu)
        hd)
    (fun _ _ _ _ => trivial)

/-! ## Boxed-Context Transfer -/

/-- **Boxed-context transfer** (the `K`-rule for deductively closed sets): if `L ⊢ φ` and
`□ψ ∈ H` for every `ψ ∈ L`, then `□φ ∈ H`. By recursion on `L`: the base case is
necessitation plus closure; the step case cuts the head assumption with the deduction
theorem and re-enters `H` through the `Kb` axiom. (The closed-set analogue of
`derive_box_from_box_context`, which is pinned to maximal consistent sets.) -/
theorem box_mem_of_boxed_context
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {H : Set (Proposition Atom)}
    (h_closed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) H) :
    ∀ (L : List (Proposition Atom)) {φ : Proposition Atom},
      DerivationTree Axioms L φ → (∀ ψ ∈ L, Proposition.box ψ ∈ H) →
      Proposition.box φ ∈ H
  | [], φ, d, _ =>
    h_closed [] _ (fun _ h => nomatch h) ⟨.necessitation φ d⟩
  | A :: L', φ, d, h_all_box => by
    have dt := deductionTheorem h_implyK h_implyS L' A φ d
    have h_box_imp : Proposition.box (A.imp φ) ∈ H :=
      box_mem_of_boxed_context h_implyK h_implyS h_k h_closed L' dt
        (fun ψ hψ => h_all_box ψ (List.mem_cons.mpr (Or.inr hψ)))
    have h_box_A : Proposition.box A ∈ H :=
      h_all_box A (List.mem_cons.mpr (Or.inl rfl))
    refine h_closed [Proposition.box (A.imp φ), Proposition.box A] _ ?_ ?_
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h_box_imp
      · rcases List.mem_cons.mp hx' with rfl | h
        · exact h_box_A
        · exact (nomatch h)
    · exact ⟨DerivationTree.modus_ponens _ _ _
        (DerivationTree.modus_ponens _ _ _
          (DerivationTree.weakening [] _ _ (.ax [] _ (h_k A φ)) (fun _ h => nomatch h))
          (DerivationTree.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))))
        (DerivationTree.assumption _ _
          (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩

/-! ## Refuting Theories -/

/-- **Implication-refuting theory**: if `φ → ψ ∉ H` for a quasi-prime `H`, there is a
quasi-prime `T ⊇ H` with `φ ∈ T` and `ψ ∉ T`. Extend `H ∪ {φ}` by
`quasi_prime_exclusion`; `ψ` stays out because deriving it would put `φ → ψ` into `H` by
the deduction theorem and closure. (The trivial-`Cons` analogue of `modal_imp_witness`.) -/
theorem imp_refuting_theory
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    {H : Set (Proposition Atom)} (hH : QuasiPrime Axioms H)
    {φ ψ : Proposition Atom} (h_not : φ.imp ψ ∉ H) :
    ∃ T, H ⊆ T ∧ QuasiPrime Axioms T ∧ φ ∈ T ∧ ψ ∉ T := by
  have h_not_psi : ψ ∉ modalDeductiveClosure Axioms (H ∪ {φ}) := by
    rintro ⟨L, hL, hd⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ := modal_deriv_imp_of_union h_implyK h_implyS hL hd
    exact h_not (hH.closed L' _ hL'_sub hL'_deriv)
  obtain ⟨T, hST, hT, hψT⟩ := quasi_prime_exclusion h_implyK h_implyS h_orE
    (fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd)
    h_not_psi
  refine ⟨T, ?_, hT, ?_, hψT⟩
  · exact Set.Subset.trans
      (Set.Subset.trans Set.subset_union_left (modal_subset_deductive_closure _ _)) hST
  · exact hST (modal_subset_deductive_closure _ _
      (Set.mem_union_right H (Set.mem_singleton_iff.mpr rfl)))

/-- **Box-refuting theory**: if `□A ∉ H` for a quasi-prime `H`, there is a quasi-prime
`T ⊇ boxInv H` with `A ∉ T`. Extend `boxInv H` by `quasi_prime_exclusion`; `A` stays out
because a derivation of `A` from `boxInv H` would place `□A` in `H` by
`box_mem_of_boxed_context`. -/
theorem box_refuting_theory
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {H : Set (Proposition Atom)} (hH : QuasiPrime Axioms H)
    {A : Proposition Atom} (h_not : Proposition.box A ∉ H) :
    ∃ T, boxInv H ⊆ T ∧ QuasiPrime Axioms T ∧ A ∉ T := by
  have h_not_A : A ∉ modalDeductiveClosure Axioms (boxInv H) := by
    rintro ⟨L, hL, ⟨d⟩⟩
    exact h_not (box_mem_of_boxed_context h_implyK h_implyS h_k hH.closed L d
      (fun ψ hψ => hL ψ hψ))
  obtain ⟨T, hST, hT, hAT⟩ := quasi_prime_exclusion h_implyK h_implyS h_orE
    (fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd)
    h_not_A
  exact ⟨T, Set.Subset.trans (modal_subset_deductive_closure _ _) hST, hT, hAT⟩

/-- **Diamond-refuting theory**: if `◇B ∈ H` and `◇A ∉ H` for a quasi-prime `H`, there is a
quasi-prime `T ⊇ boxInv H` with `B ∈ T` and `A ∉ T`. Extend `boxInv H ∪ {B}`; `A` stays
out because a derivation `boxInv H, B ⊢ A` yields `□(B → A) ∈ H` by the deduction theorem
plus `box_mem_of_boxed_context`, whence `◇A ∈ H` by `Kd` and `◇B ∈ H` — contradiction.
This is the only place the `Kd` axiom enters the canonical construction. -/
theorem dia_refuting_theory
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    {H : Set (Proposition Atom)} (hH : QuasiPrime Axioms H)
    {A B : Proposition Atom} (h_dia_B : (◇B) ∈ H) (h_not : (◇A) ∉ H) :
    ∃ T, boxInv H ⊆ T ∧ QuasiPrime Axioms T ∧ B ∈ T ∧ A ∉ T := by
  have h_not_A : A ∉ modalDeductiveClosure Axioms (boxInv H ∪ {B}) := by
    rintro ⟨L, hL, hd⟩
    obtain ⟨L', hL'_sub, ⟨d'⟩⟩ := modal_deriv_imp_of_union h_implyK h_implyS hL hd
    have h_box_imp : Proposition.box (B.imp A) ∈ H :=
      box_mem_of_boxed_context h_implyK h_implyS h_k hH.closed L' d'
        (fun ψ hψ => hL'_sub ψ hψ)
    have h_dia_A : (◇A) ∈ H := by
      refine hH.closed [Proposition.box (B.imp A), ◇B] _ ?_ ?_
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h_box_imp
        · rcases List.mem_cons.mp hx' with rfl | h
          · exact h_dia_B
          · exact (nomatch h)
      · exact ⟨DerivationTree.modus_ponens _ _ _
          (DerivationTree.modus_ponens _ _ _
            (DerivationTree.weakening [] _ _ (.ax [] _ (h_kdia B A)) (fun _ h => nomatch h))
            (DerivationTree.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))))
          (DerivationTree.assumption _ _
            (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩
    exact h_not h_dia_A
  obtain ⟨T, hST, hT, hAT⟩ := quasi_prime_exclusion h_implyK h_implyS h_orE
    (fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd)
    h_not_A
  refine ⟨T, ?_, hT, ?_, hAT⟩
  · exact Set.Subset.trans
      (Set.Subset.trans Set.subset_union_left (modal_subset_deductive_closure _ _)) hST
  · exact hST (modal_subset_deductive_closure _ _
      (Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl)))

/-! ## Segment Realization -/

/-- **Head realization**: any underivable formula is omitted by some quasi-prime theory —
extend the deductive closure of `∅` by `quasi_prime_exclusion`. -/
theorem quasi_head_realization
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    {φ : Proposition Atom} (h_nd : ¬ Derivable Axioms φ) :
    ∃ T, QuasiPrime Axioms T ∧ φ ∉ T := by
  have h_not : φ ∉ modalDeductiveClosure Axioms (∅ : Set (Proposition Atom)) := by
    rintro ⟨L, hL, ⟨d⟩⟩
    exact h_nd ⟨.weakening L [] φ d (fun x hx => absurd (hL x hx) (fun h => h))⟩
  obtain ⟨T, _, hT, hφT⟩ := quasi_prime_exclusion h_implyK h_implyS h_orE
    (fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd)
    h_not
  exact ⟨T, hT, hφT⟩

/-- **Segment realization**: any underivable formula is omitted by the head of some segment
(realize the quasi-prime theory from `quasi_head_realization` via `CKSegment.ofHead`). -/
theorem segment_realization
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    {φ : Proposition Atom} (h_nd : ¬ Derivable Axioms φ) :
    ∃ s : CKSegment Axioms, φ ∉ s.head := by
  obtain ⟨T, hT, hφT⟩ := quasi_head_realization h_implyK h_implyS h_orE h_nd
  exact ⟨CKSegment.ofHead hT, hφT⟩

end Cslib.Logic.Modal
