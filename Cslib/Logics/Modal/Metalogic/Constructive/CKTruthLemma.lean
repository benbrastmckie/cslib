/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum
public import Cslib.Logics.Modal.Metalogic.Constructive.Forcing

/-! # Truth Lemma for the Constructive Modal Segment Model

This module proves the truth lemma for the `CK` canonical segment model: `CKForces` over
`cmreach`/`cval`/`cbotForces` coincides with head membership. Transliterated from ianshil/CK
`Completeness_seg/general_seg_completeness.v` (`truth_lemma`).

The `≤`-freedom of segments does the modal work: segments with the same head but different
tails are `≤`-interchangeable, so the backward `box`/`diamond` cases refute forcing by
re-tailing the current head —

- **box**: against the *maximal* tail (`CKSegment.ofHead`), which contains the
  box-refuting theory of `box_refuting_theory`;
- **diamond**: against the *restricted* tail (`diamRefutingSegment`) all of whose members
  omit the witness formula; the restricted tail still satisfies the diamond-witness field
  by `dia_refuting_theory` (this is where `Kd` enters, and the ∀∃ diamond clause of
  `CKForces` is exactly what permits the re-tailing — under the plain `∃` clause the
  diamond-backward case is *impossible* for bare `CK`, cf. `Forcing.lean`).

No Fischer-Servi axiom (`Cd`/`Idb`) and no frame condition is consumed anywhere.

## Main Results

- `mem_of_axiom`/`mem_head_mp`: closure helpers for deductively closed theories.
- `diamRefutingSegment`: the restricted-tail segment refuting an unwarranted `◇A`.
- `ck_truth_lemma`: `CKForces cmreach cval cbotForces s φ ↔ φ ∈ s.head`.

## References

* ianshil/CK `Completeness_seg/general_seg_completeness.v`, `truth_lemma`.
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 5.6
  (the classical template).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Closure Helpers -/

/-- Every axiom instance belongs to every deductively closed theory. -/
theorem mem_of_axiom {Axioms : Proposition Atom → Prop}
    {H : Set (Proposition Atom)}
    (h_closed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) H)
    {φ : Proposition Atom} (h_ax : Axioms φ) : φ ∈ H :=
  h_closed [] φ (fun _ h => nomatch h) ⟨.ax [] φ h_ax⟩

/-- Deductively closed theories are closed under modus ponens. -/
theorem mem_head_mp {Axioms : Proposition Atom → Prop}
    {H : Set (Proposition Atom)}
    (h_closed : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) H)
    {A B : Proposition Atom} (h_imp : A.imp B ∈ H) (hA : A ∈ H) : B ∈ H := by
  refine h_closed [A.imp B, A] B ?_ ?_
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h_imp
    · rcases List.mem_cons.mp hx' with rfl | h
      · exact hA
      · exact (nomatch h)
  · exact ⟨DerivationTree.modus_ponens _ _ _
      (DerivationTree.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))
      (DerivationTree.assumption _ _
        (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))⟩

/-! ## The Diamond-Refuting Segment -/

/-- The diamond-refuting segment for `◇A ∉ s.head`: same head as `s`, with the *restricted*
tail of all quasi-prime supersets of `boxInv s.head` omitting `A`. Box reflection holds by
construction, and the diamond-witness field survives the restriction by
`dia_refuting_theory` (any `◇B ∈ head` has a witness theory omitting `A`, since `◇A ∉ head`).
Because it shares `s`'s head, it is a `≤`-successor of `s` — instantiating the ∀∃ diamond
clause of `CKForces` at it refutes `◇A`. -/
def diamRefutingSegment {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (s : CKSegment Axioms) {A : Proposition Atom} (h_not : (◇A) ∉ s.head) :
    CKSegment Axioms where
  head := s.head
  tail := {t | QuasiPrime Axioms t ∧ boxInv s.head ⊆ t ∧ A ∉ t}
  head_qprime := s.head_qprime
  tail_qprime := fun _ ht => ht.1
  box_reflect := fun _ hB _ ht => ht.2.1 hB
  diam_witness := fun B hB => by
    obtain ⟨T, hsub, hT, hBT, hAT⟩ :=
      dia_refuting_theory h_implyK h_implyS h_orE h_k h_kdia s.head_qprime hB h_not
    exact ⟨T, ⟨hT, hsub, hAT⟩, hBT⟩

@[simp] theorem diamRefutingSegment_head {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (s : CKSegment Axioms) {A : Proposition Atom} (h_not : (◇A) ∉ s.head) :
    (diamRefutingSegment h_implyK h_implyS h_orE h_k h_kdia s h_not).head = s.head := rfl

/-! ## The Truth Lemma -/

/-- **Truth lemma** for the `CK` canonical segment model: `CKForces` (over `cmreach`,
`cval`, and the fallibility predicate `cbotForces`) coincides with head membership.

By induction on the formula, generalizing over the segment. The `atom`/`bot` cases are
definitional; `and`/`or`/`imp`-forward use closure (and the disjunction property);
`imp`-backward re-heads via `imp_refuting_theory`; `box`-backward re-tails to the maximal
tail (`CKSegment.ofHead`) containing the `box_refuting_theory` witness; `diamond`-backward
re-tails to `diamRefutingSegment`. No `Cd`, `Idb`, or `Nd` instance is used. -/
theorem ck_truth_lemma {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_k : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_kdia : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ))))
    (s : CKSegment Axioms) (φ : Proposition Atom) :
    CKForces cmreach cval cbotForces s φ ↔ φ ∈ s.head := by
  induction φ generalizing s with
  | atom p => exact Iff.rfl
  | bot => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    constructor
    · intro hf
      by_contra h_not
      obtain ⟨T, hHT, hT, hφT, hψT⟩ :=
        imp_refuting_theory h_implyK h_implyS h_orE s.head_qprime h_not
      exact hψT ((ihψ (CKSegment.ofHead hT)).mp
        (hf (CKSegment.ofHead hT) hHT ((ihφ (CKSegment.ofHead hT)).mpr hφT)))
    · intro hmem s' hle hfφ
      exact (ihψ s').mpr
        (mem_head_mp s'.head_qprime.closed (hle hmem) ((ihφ s').mp hfφ))
  | and φ ψ ihφ ihψ =>
    constructor
    · rintro ⟨hfφ, hfψ⟩
      exact mem_head_mp s.head_qprime.closed
        (mem_head_mp s.head_qprime.closed
          (mem_of_axiom s.head_qprime.closed (h_andI φ ψ)) ((ihφ s).mp hfφ))
        ((ihψ s).mp hfψ)
    · intro hmem
      exact ⟨(ihφ s).mpr (mem_head_mp s.head_qprime.closed
                (mem_of_axiom s.head_qprime.closed (h_andE1 φ ψ)) hmem),
             (ihψ s).mpr (mem_head_mp s.head_qprime.closed
                (mem_of_axiom s.head_qprime.closed (h_andE2 φ ψ)) hmem)⟩
  | or φ ψ ihφ ihψ =>
    constructor
    · rintro (hfφ | hfψ)
      · exact mem_head_mp s.head_qprime.closed
          (mem_of_axiom s.head_qprime.closed (h_orI1 φ ψ)) ((ihφ s).mp hfφ)
      · exact mem_head_mp s.head_qprime.closed
          (mem_of_axiom s.head_qprime.closed (h_orI2 φ ψ)) ((ihψ s).mp hfψ)
    · intro hmem
      rcases s.head_qprime.disj hmem with h | h
      · exact Or.inl ((ihφ s).mpr h)
      · exact Or.inr ((ihψ s).mpr h)
  | box φ ihφ =>
    constructor
    · intro hf
      by_contra h_not
      obtain ⟨T, hsub, hT, hAT⟩ :=
        box_refuting_theory h_implyK h_implyS h_orE h_k s.head_qprime h_not
      have hr : cmreach (CKSegment.ofHead s.head_qprime) (CKSegment.ofHead hT) :=
        ⟨hT, hsub⟩
      exact hAT ((ihφ (CKSegment.ofHead hT)).mp
        (hf (CKSegment.ofHead s.head_qprime) (Set.Subset.refl _) (CKSegment.ofHead hT) hr))
    · intro hmem s' hle Q hr
      exact (ihφ Q).mpr (s'.box_reflect φ (hle hmem) Q.head hr)
  | diamond φ ihφ =>
    constructor
    · intro hf
      by_contra h_not
      obtain ⟨Q, hr, hfQ⟩ :=
        hf (diamRefutingSegment h_implyK h_implyS h_orE h_k h_kdia s h_not)
          (Set.Subset.refl _)
      exact hr.2.2 ((ihφ Q).mp hfQ)
    · intro hmem s' hle
      obtain ⟨t, ht_mem, hφt⟩ := s'.diam_witness φ (hle hmem)
      exact ⟨CKSegment.ofHead (s'.tail_qprime t ht_mem), ht_mem, (ihφ _).mpr hφt⟩

end Cslib.Logic.Modal
