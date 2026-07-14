/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.PrimeExclusion
public import Cslib.Foundations.Logic.Metalogic.Consistency
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Logics.Modal.Metalogic.DeductionTheorem
public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Data.ListHelpers

/-! # Prime Theories for Intuitionistic Modal Logic

This module provides the intuitionistic modal prime-theory layer: a thin, axiom-parametric
wrapper over the reused generic `Metalogic.prime_exclusion`
(`Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`), instantiated at
`F = Modal.Proposition Atom`. It mirrors the propositional
`Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` development, transliterated to the
modal derivation system `modalDerivationSystem Axioms`
(`Cslib/Logics/Modal/Metalogic/DerivationTree.lean`).

Worlds for the intuitionistic modal canonical model (`CanonicalModel.lean`) are **prime
theories**: consistent, deductively-closed, disjunction-property sets, rather than the
classical maximal consistent sets used by `Cslib/Logics/Modal/Metalogic/MCS.lean`.

## Main Definitions

- `ModalSetConsistent`, `ModalPrimeTheory`: prime-theory predicates over `modalDerivationSystem`.
- `modalDeductiveClosure`: the deductive closure of a set under `Axioms`.
- `modal_imp_witness`: the implication-witness lemma (build a theory forcing `φ` but not `ψ`
  when `φ → ψ` is not a theorem).
- `modal_prime_exclusion`: the prime-exclusion (Lindenbaum-for-prime-theories) lemma.

Every declaration is parameterized over an `Axioms : Proposition Atom → Prop` predicate with
the base intuitionistic axioms (`implyK`, `implyS`, `efq`, `orE`) as explicit hypotheses;
`h_efq` is kept as a hypothesis **separate** from `h_implyK`/`h_implyS`/`h_orE` so that the
minimal modal logic instantiation (task 495) can omit it.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5,
  Section 5.1, Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## Prime Theory Predicates -/

/-- Set consistency for a parameterized modal derivation system. -/
abbrev ModalSetConsistent (Axioms : Proposition Atom → Prop)
    (S : Set (Proposition Atom)) : Prop :=
  Metalogic.SetConsistent (modalDerivationSystem Axioms) S

/-- A prime modal theory: consistent, deductively closed, and satisfying the disjunction
property (`φ ∨ ψ ∈ S → φ ∈ S ∨ ψ ∈ S`). Worlds of the intuitionistic modal canonical model
(`CanonicalModel.lean`) are prime modal theories. -/
abbrev ModalPrimeTheory (Axioms : Proposition Atom → Prop)
    (S : Set (Proposition Atom)) : Prop :=
  Metalogic.PrimeAdmissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms) S

/-! ## Deductive Closure -/

/-- The deductive closure of a set `S` w.r.t. the modal axiom predicate `Axioms`. -/
def modalDeductiveClosure (Axioms : Proposition Atom → Prop) (S : Set (Proposition Atom)) :
    Set (Proposition Atom) :=
  {φ | ∃ L : List (Proposition Atom),
    (∀ x ∈ L, x ∈ S) ∧ (modalDerivationSystem Axioms).Deriv L φ}

/-- `S ⊆ modalDeductiveClosure Axioms S`. -/
theorem modal_subset_deductive_closure (Axioms : Proposition Atom → Prop)
    (S : Set (Proposition Atom)) :
    S ⊆ modalDeductiveClosure Axioms S :=
  fun φ hφ => ⟨[φ],
    fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ hφ,
    (modalDerivationSystem Axioms).assumption (List.mem_cons.mpr (Or.inl rfl))⟩

/-- If every element of `L` is derivable from some finite list in `S`, then any `φ` derivable
from `L` is also derivable from some finite list in `S`.

The proof works by induction on `L`, using the deduction theorem to "cut" each element `a`
out of the context, replacing it with its witness derivation from `S`. -/
theorem modal_deriv_from_closure_to_S
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)}
    (L : List (Proposition Atom))
    (hL : ∀ x ∈ L, ∃ Lx : List (Proposition Atom),
      (∀ y ∈ Lx, y ∈ S) ∧ (modalDerivationSystem Axioms).Deriv Lx x)
    (φ : Proposition Atom)
    (hd : (modalDerivationSystem Axioms).Deriv L φ) :
    ∃ L' : List (Proposition Atom),
      (∀ y ∈ L', y ∈ S) ∧ (modalDerivationSystem Axioms).Deriv L' φ := by
  induction L generalizing φ with
  | nil => exact ⟨[], fun _ h => (nomatch h), hd⟩
  | cons a L' ih =>
    have hd_dt := hasDeductionTheorem h_implyK h_implyS hd
    obtain ⟨L_imp, hL_imp_sub, hL_imp_deriv⟩ :=
      ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx))) (a → φ) hd_dt
    obtain ⟨La, hLa_sub, hLa_deriv⟩ := hL a (List.mem_cons.mpr (Or.inl rfl))
    exact ⟨La ++ L_imp,
      fun y hy => by
        rw [List.mem_append] at hy
        exact hy.elim (hLa_sub y) (hL_imp_sub y),
      (modalDerivationSystem Axioms).mp
        ((modalDerivationSystem Axioms).weakening hL_imp_deriv
          (fun x hx => List.mem_append.mpr (Or.inr hx)))
        ((modalDerivationSystem Axioms).weakening hLa_deriv
          (fun x hx => List.mem_append.mpr (Or.inl hx)))⟩

/-- The deductive closure is deductively closed. -/
theorem modalDeductiveClosure_closed
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)}
    (L : List (Proposition Atom)) (φ : Proposition Atom)
    (hL : ∀ x ∈ L, x ∈ modalDeductiveClosure Axioms S)
    (hd : (modalDerivationSystem Axioms).Deriv L φ) :
    φ ∈ modalDeductiveClosure Axioms S :=
  modal_deriv_from_closure_to_S h_implyK h_implyS L (fun x hx => hL x hx) φ hd

/-- If `S` is consistent, the deductive closure of `S` is consistent. -/
theorem modalDeductiveClosure_consistent
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)}
    (hS : ModalSetConsistent Axioms S) :
    ModalSetConsistent Axioms (modalDeductiveClosure Axioms S) := by
  intro L hL hd
  obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
    modal_deriv_from_closure_to_S h_implyK h_implyS L (fun x hx => hL x hx) _ hd
  exact hS L' hL'_sub hL'_deriv

/-- The deductive closure of a consistent set is admissible (consistent and deductively
closed). -/
theorem modalDeductiveClosure_is_admissible
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)}
    (hS : ModalSetConsistent Axioms S) :
    Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
      (modalDeductiveClosure Axioms S) :=
  ⟨modalDeductiveClosure_consistent h_implyK h_implyS hS,
   fun L φ hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ hL hd⟩

/-! ## Cut Lemma for Union Contexts -/

/-- If `L ⊢ ψ` and `L ⊆ S ∪ {φ}`, then `∃ L' ⊆ S, L' ⊢ φ → ψ`.

Uses `deductionWithMem` + `removeAll` to eliminate all occurrences of `φ` from the derivation
context. -/
theorem modal_deriv_imp_of_union
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)}
    {L : List (Proposition Atom)} {φ ψ : Proposition Atom}
    (hL : ∀ x ∈ L, x ∈ S ∪ {φ})
    (hd : (modalDerivationSystem Axioms).Deriv L ψ) :
    ∃ L' : List (Proposition Atom),
      (∀ x ∈ L', x ∈ S) ∧
      (modalDerivationSystem Axioms).Deriv L' (φ → ψ) := by
  obtain ⟨d⟩ := hd
  have d_ext := DerivationTree.weakening L (φ :: L) ψ d
    (fun x hx => List.mem_cons.mpr (Or.inr hx))
  have d_dt := deductionTheorem h_implyK h_implyS L φ ψ d_ext
  by_cases hφL : φ ∈ L
  · -- φ ∈ L: use deductionWithMem to remove ALL occurrences of φ
    have d_mem := deductionWithMem h_implyK h_implyS L φ (φ → ψ) d_dt hφL
    have h_rem_sub : ∀ x ∈ removeAll L φ, x ∈ S := by
      intro x hx
      simp only [removeAll, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not] at hx
      obtain ⟨hx_in, hx_ne⟩ := hx
      rcases hL x hx_in with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hx_ne
    let ctx := removeAll L φ
    have d_is : DerivationTree Axioms (Atom := Atom) ctx
        ((φ.imp (φ.imp ψ)).imp ((φ.imp φ).imp (φ.imp ψ))) :=
      .weakening [] ctx _ (.ax [] _ (h_implyS φ φ ψ)) (fun _ h => nomatch h)
    have d_step1 := DerivationTree.modus_ponens ctx _ _ d_is d_mem
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
    have d_final := DerivationTree.modus_ponens ctx _ _ d_step1 d_id_w
    exact ⟨ctx, h_rem_sub, ⟨d_final⟩⟩
  · -- φ ∉ L: L ⊆ S already
    have hL_S : ∀ x ∈ L, x ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hx) hφL
    exact ⟨L, hL_S, ⟨d_dt⟩⟩

/-! ## EFQ Composition Derivation -/

/-- `[¬φ] ⊢ φ → ψ` via EFQ composition. -/
noncomputable def modalNegPhiImpPsi {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (φ ψ : Proposition Atom) :
    DerivationTree Axioms [Proposition.neg φ] (φ.imp ψ) :=
  let efq_ax := DerivationTree.ax (Atom := Atom) [] (Proposition.bot.imp ψ) (h_efq ψ)
  let ik := DerivationTree.ax (Atom := Atom) []
    ((Proposition.bot.imp ψ).imp (φ.imp (Proposition.bot.imp ψ)))
    (h_implyK (Proposition.bot.imp ψ) φ)
  let step3 := DerivationTree.modus_ponens [] _ _ ik efq_ax
  let is_ax := DerivationTree.ax (Atom := Atom) []
    ((φ.imp (Proposition.bot.imp ψ)).imp ((Proposition.neg φ).imp (φ.imp ψ)))
    (h_implyS φ Proposition.bot ψ)
  let step5 := DerivationTree.modus_ponens [] _ _ is_ax step3
  let step5w := DerivationTree.weakening [] [Proposition.neg φ] _ step5
    (fun _ h => nomatch h)
  DerivationTree.modus_ponens [Proposition.neg φ] (Proposition.neg φ) (φ.imp ψ)
    step5w
    (DerivationTree.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))

/-- Prop-level EFQ composition. -/
theorem modalNegPhiImpPsi_deriv {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (φ ψ : Proposition Atom) :
    (modalDerivationSystem Axioms).Deriv [Proposition.neg φ] (φ.imp ψ) :=
  ⟨modalNegPhiImpPsi h_implyK h_implyS h_efq φ ψ⟩

/-! ## Implication Witness Lemma -/

/-- **Implication Witness Lemma**: If `S` is admissible and `φ → ψ ∉ S`, then the deductive
closure of `S ∪ {φ}` is an admissible `T ⊇ S` with `φ ∈ T` and `ψ ∉ T`.

`h_efq` is a hypothesis separate from `h_implyK`/`h_implyS` so the minimal modal instantiation
(task 495) can omit it. -/
theorem modal_imp_witness
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    {S : Set (Proposition Atom)}
    (h_adm : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms) S)
    {φ ψ : Proposition Atom} (h_not : (φ → ψ) ∉ S) :
    ∃ T : Set (Proposition Atom),
      S ⊆ T ∧
      Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms) T ∧
      φ ∈ T ∧ ψ ∉ T := by
  -- Step 1: S ∪ {φ} is consistent (EFQ argument)
  have h_cons_union : ModalSetConsistent Axioms (S ∪ {φ}) := by
    intro L hL hd
    obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
      modal_deriv_imp_of_union h_implyK h_implyS hL hd
    have h_neg_phi : (¬φ) ∈ S := h_adm.2 L' _ hL'_sub hL'_deriv
    have h_imp_psi : (φ → ψ) ∈ S := by
      apply h_adm.2 [(¬φ)] (φ → ψ)
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_neg_phi
      · exact modalNegPhiImpPsi_deriv h_implyK h_implyS h_efq φ ψ
    exact h_not h_imp_psi
  -- Step 2: consistency is preserved under deductive closure
  have h_cons_cl : ModalSetConsistent Axioms (modalDeductiveClosure Axioms (S ∪ {φ})) :=
    modalDeductiveClosure_consistent h_implyK h_implyS h_cons_union
  refine ⟨modalDeductiveClosure Axioms (S ∪ {φ}), ?_, ?_, ?_, ?_⟩
  · exact Set.Subset.trans Set.subset_union_left (modal_subset_deductive_closure _ _)
  · exact ⟨h_cons_cl, fun L φ' hL hd => modalDeductiveClosure_closed h_implyK h_implyS L φ' hL hd⟩
  · exact modal_subset_deductive_closure _ _
      (Set.mem_union_right S (Set.mem_singleton_iff.mpr rfl))
  · intro ⟨L, hL_sub, hL_deriv⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ := modal_deriv_imp_of_union h_implyK h_implyS hL_sub hL_deriv
    exact h_not (h_adm.2 L' _ hL'_sub hL'_deriv)

/-! ## Prime Exclusion Lemma (Intuitionistic Modal) -/

/-- **Prime Exclusion Lemma for Modal Theories**: given an admissible set `S` with
`phi ∉ S`, there exists a prime modal theory `T ⊇ S` with `phi ∉ T`.

Thin wrapper around `Metalogic.prime_exclusion` with `Cons := ModalSetConsistent Axioms`,
`cl := modalDeductiveClosure Axioms`, and the EFQ bridge supplied via `h_efq`. `h_efq` is kept
separate from `h_implyK`/`h_implyS`/`h_orE` so the minimal modal instantiation (task 495)
can omit it.

See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5. -/
theorem modal_prime_exclusion
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_orE : ∀ A B χ : Proposition Atom, Axioms (Cslib.Logic.Axioms.OrE A B χ))
    {S : Set (Proposition Atom)}
    (h_adm : Metalogic.Admissible (modalDerivationSystem Axioms) (ModalSetConsistent Axioms) S)
    {phi : Proposition Atom} (h_not : phi ∉ S) :
    ∃ T, S ⊆ T ∧ ModalPrimeTheory Axioms T ∧ phi ∉ T :=
  Metalogic.prime_exclusion
    (modalDerivationSystem Axioms) (ModalSetConsistent Axioms)
    h_adm h_not
    -- orE schema as an empty-context derivation
    (fun A B χ => ⟨.ax [] _ (h_orE A B χ)⟩)
    -- deductive closure operator and its laws
    (modalDeductiveClosure Axioms)
    (modal_subset_deductive_closure Axioms)
    (fun {_X _ψ} h => h)
    (fun {_X} hX => modalDeductiveClosure_is_admissible h_implyK h_implyS hX)
    -- EFQ bridge: phi ∈ cl X when X is inconsistent
    (fun {X} h_not_cons => by
      simp only [ModalSetConsistent, Metalogic.SetConsistent, Metalogic.Consistent,
        not_forall, not_not] at h_not_cons
      obtain ⟨Linc, hLinc_sub, hLinc_bot⟩ := h_not_cons
      let efq : DerivationTree Axioms (Atom := Atom) [] ((⊥ : Proposition Atom).imp phi) :=
        .ax [] _ (h_efq phi)
      let efq_w := DerivationTree.weakening [] Linc _ efq (fun _ h => nomatch h)
      obtain ⟨d_bot⟩ := hLinc_bot
      let d_phi := DerivationTree.modus_ponens Linc _ _ efq_w d_bot
      exact ⟨Linc, hLinc_sub, ⟨d_phi⟩⟩)
    -- cut witness via modal_deriv_imp_of_union
    (fun {U _L a _b} hL hd =>
      modal_deriv_imp_of_union h_implyK h_implyS
        (fun x hx => by
          rcases Set.mem_insert_iff.mp (hL x hx) with rfl | hu
          · exact Set.mem_union_right U (Set.mem_singleton_iff.mpr rfl)
          · exact Set.mem_union_left _ hu)
        hd)
    -- Cons preserved by chains: consistency of ⋃₀ C via finite_list_in_chain_member
    (fun C hchain hCne hCsub L hL hd =>
      let ⟨T', hT'C, hLT'⟩ := Metalogic.finite_list_in_chain_member hchain hCne L hL
      (hCsub hT'C).2.1.1 L hLT' hd)

end Cslib.Logic.Modal
