/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Metalogic.PrimeExclusion
public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem
public import Cslib.Logics.Propositional.Metalogic.GenericLindenbaum
public import Cslib.Logics.Propositional.Metalogic.MCS
public import Cslib.Logics.Propositional.Metalogic.Soundness

/-! # Deductively Closed Consistent Sets for Intuitionistic Propositional Logic

This module defines DCCS for IntPropAxiom and proves the implication witness lemma.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 5.1, Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Helpers

variable {Atom : Type*}

attribute [local instance] Classical.propDecidable

/-! ## DCCS Definition -/

/-- A deductively closed consistent set (DCCS) for IntPropAxiom. -/
def IntDCCS (S : Set (PL.Proposition Atom)) : Prop :=
  PropSetConsistent IntPropAxiom S ∧
  ∀ (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) → (propDerivationSystem IntPropAxiom).Deriv L φ → φ ∈ S

/-! ## Basic DCCS Properties -/

/-- `⊥ ∉ S` for any IntDCCS `S`. -/
theorem int_dccs_bot_not_mem {S : Set (PL.Proposition Atom)}
    (h : IntDCCS S) : (⊥ : PL.Proposition Atom) ∉ S := by
  intro h_bot
  exact h.1 [⊥]
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_bot)
    ((propDerivationSystem IntPropAxiom).assumption (List.mem_cons.mpr (Or.inl rfl)))

/-- Modus ponens closure: if `φ → ψ ∈ S` and `φ ∈ S`, then `ψ ∈ S`. -/
theorem int_dccs_imp_property {S : Set (PL.Proposition Atom)}
    (h : IntDCCS S) {φ ψ : PL.Proposition Atom}
    (h_imp : (φ → ψ) ∈ S) (h_phi : φ ∈ S) : ψ ∈ S := by
  apply h.2 [(φ → ψ), φ] ψ
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · exact (propDerivationSystem IntPropAxiom).mp
      ((propDerivationSystem IntPropAxiom).assumption
        (List.mem_cons.mpr (Or.inl rfl)))
      ((propDerivationSystem IntPropAxiom).assumption
        (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-! ## EFQ Composition Derivation -/

/-- `[¬φ] ⊢ φ → ψ` via EFQ composition. -/
noncomputable def intNegPhiImpPsi (φ ψ : PL.Proposition Atom) :
    DerivationTree IntPropAxiom [Proposition.neg φ] (φ.imp ψ) :=
  let efq_ax := DerivationTree.ax (Atom := Atom) [] (Proposition.bot.imp ψ) (.efq ψ)
  let ik := DerivationTree.ax (Atom := Atom) []
    ((Proposition.bot.imp ψ).imp (φ.imp (Proposition.bot.imp ψ)))
    (.implyK (Proposition.bot.imp ψ) φ)
  let step3 := DerivationTree.modus_ponens [] _ _ ik efq_ax
  let is_ax := DerivationTree.ax (Atom := Atom) []
    ((φ.imp (Proposition.bot.imp ψ)).imp ((Proposition.neg φ).imp (φ.imp ψ)))
    (.implyS φ Proposition.bot ψ)
  let step5 := DerivationTree.modus_ponens [] _ _ is_ax step3
  let step5w := DerivationTree.weakening [] [Proposition.neg φ] _ step5
    (fun _ h => nomatch h)
  DerivationTree.modus_ponens [Proposition.neg φ] (Proposition.neg φ) (φ.imp ψ)
    step5w
    (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))

/-- Prop-level EFQ composition. -/
theorem intNegPhiImpPsi_deriv (φ ψ : PL.Proposition Atom) :
    (propDerivationSystem IntPropAxiom).Deriv [Proposition.neg φ] (φ.imp ψ) :=
  ⟨intNegPhiImpPsi φ ψ⟩

/-! ## Compiling Derivations from Closure Elements -/

/-- If every element of L is derivable from some list in S,
then any φ derivable from L is also derivable from some list in S.

The proof works by induction on L, using the deduction theorem to
"cut" each element `a` out of the context, replacing it with its
witness derivation from S. -/
theorem int_deriv_from_closure_to_S {S : Set (PL.Proposition Atom)}
    (L : List (PL.Proposition Atom))
    (hL : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
      (∀ y ∈ Lx, y ∈ S) ∧ (propDerivationSystem IntPropAxiom).Deriv Lx x)
    (φ : PL.Proposition Atom)
    (hd : (propDerivationSystem IntPropAxiom).Deriv L φ) :
    ∃ L' : List (PL.Proposition Atom),
      (∀ y ∈ L', y ∈ S) ∧ (propDerivationSystem IntPropAxiom).Deriv L' φ :=
  generic_deriv_from_closure_to_S IntPropAxiom.mem_implyK IntPropAxiom.mem_implyS L hL φ hd

/-! ## Cut Lemma for Union Contexts -/

/-- If `L ⊢ ψ` and `L ⊆ S ∪ {φ}`, then `∃ L' ⊆ S, L' ⊢ φ → ψ`.

Uses `deductionWithMem` + `removeAll` to eliminate all occurrences of `φ`
from the derivation context. -/
theorem int_deriv_imp_of_union
    {S : Set (PL.Proposition Atom)}
    {L : List (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (hL : ∀ x ∈ L, x ∈ S ∪ {φ})
    (hd : (propDerivationSystem IntPropAxiom).Deriv L ψ) :
    ∃ L' : List (PL.Proposition Atom),
      (∀ x ∈ L', x ∈ S) ∧
      (propDerivationSystem IntPropAxiom).Deriv L' (φ → ψ) :=
  generic_deriv_imp_of_union IntPropAxiom.mem_implyK IntPropAxiom.mem_implyS hL hd

/-! ## Deductive Closure -/

/-- The deductive closure of a set `S` w.r.t. IntPropAxiom. -/
def intDeductiveClosure (S : Set (PL.Proposition Atom)) :
    Set (PL.Proposition Atom) :=
  {φ | ∃ L : List (PL.Proposition Atom),
    (∀ x ∈ L, x ∈ S) ∧ (propDerivationSystem IntPropAxiom).Deriv L φ}

/-- `S ⊆ intDeductiveClosure S`. -/
theorem int_subset_deductive_closure (S : Set (PL.Proposition Atom)) :
    S ⊆ intDeductiveClosure S :=
  fun φ hφ => ⟨[φ],
    fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ hφ,
    (propDerivationSystem IntPropAxiom).assumption (List.mem_cons.mpr (Or.inl rfl))⟩

/-- The deductive closure is deductively closed. -/
theorem intDeductiveClosure_dccs_closed (S : Set (PL.Proposition Atom))
    (L : List (PL.Proposition Atom)) (φ : PL.Proposition Atom)
    (hL : ∀ x ∈ L, x ∈ intDeductiveClosure S)
    (hd : (propDerivationSystem IntPropAxiom).Deriv L φ) :
    φ ∈ intDeductiveClosure S :=
  int_deriv_from_closure_to_S L (fun x hx => hL x hx) φ hd

/-- If `S` is consistent, the deductive closure of `S` is consistent. -/
theorem intDeductiveClosure_consistent {S : Set (PL.Proposition Atom)}
    (hS : PropSetConsistent IntPropAxiom S) :
    PropSetConsistent IntPropAxiom (intDeductiveClosure S) := by
  intro L hL hd
  obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
    int_deriv_from_closure_to_S L (fun x hx => hL x hx) _ hd
  exact hS L' hL'_sub hL'_deriv

/-- The deductive closure of a consistent set is a DCCS. -/
theorem intDeductiveClosure_is_dccs {S : Set (PL.Proposition Atom)}
    (hS : PropSetConsistent IntPropAxiom S) :
    IntDCCS (intDeductiveClosure S) :=
  ⟨intDeductiveClosure_consistent hS,
   fun L φ hL hd => intDeductiveClosure_dccs_closed S L φ hL hd⟩

/-! ## Implication Witness Lemma -/

/-- **Implication Witness Lemma**: If `S` is IntDCCS and `φ → ψ ∉ S`,
then the deductive closure of `S ∪ {φ}` is a DCCS `T ⊇ S` with
`φ ∈ T` and `ψ ∉ T`. -/
theorem int_imp_witness {S : Set (PL.Proposition Atom)}
    (h_dccs : IntDCCS S) {φ ψ : PL.Proposition Atom}
    (h_not : (φ → ψ) ∉ S) :
    ∃ T : Set (PL.Proposition Atom),
      S ⊆ T ∧ IntDCCS T ∧ φ ∈ T ∧ ψ ∉ T := by
  -- h_cons_ext: prove consistency of GenericDeductiveClosure IntPropAxiom (S ∪ {φ})
  -- by: (1) EFQ argument for S ∪ {φ} consistency, (2) closure preserves consistency
  obtain ⟨T, hST, hT_gen, hφT, hψT⟩ :=
    generic_imp_witness (Cons := PropSetConsistent IntPropAxiom)
      IntPropAxiom.mem_implyK IntPropAxiom.mem_implyS
      (h_theory := h_dccs)
      (h_cons_ext := fun h_theory h_not' => by
        -- Step 1: S ∪ {φ} is consistent (EFQ argument)
        have h_cons_union : PropSetConsistent IntPropAxiom (S ∪ {φ}) := by
          intro L hL hd
          obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
            generic_deriv_imp_of_union IntPropAxiom.mem_implyK IntPropAxiom.mem_implyS hL hd
          have h_neg_phi : (¬φ) ∈ S := h_theory.2 L' _ hL'_sub hL'_deriv
          have h_imp_psi : (φ → ψ) ∈ S := by
            apply h_theory.2 [(¬φ)] (φ → ψ)
            · intro x hx
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_neg_phi
            · exact intNegPhiImpPsi_deriv φ ψ
          exact h_not' h_imp_psi
        -- Step 2: consistency is preserved under generic deductive closure
        -- (GenericDeductiveClosure IntPropAxiom = intDeductiveClosure definitionally)
        exact intDeductiveClosure_consistent h_cons_union)
      h_not
  exact ⟨T, hST, hT_gen, hφT, hψT⟩

/-! ## Prime DCCSs for Intuitionistic Logic -/

/-- A prime DCCS: an IntDCCS satisfying the disjunction property.
If `φ ∨ ψ ∈ S`, then `φ ∈ S` or `ψ ∈ S`. -/
def IntPrimeDCCS (S : Set (PL.Proposition Atom)) : Prop :=
  IntDCCS S ∧
  ∀ (φ ψ : PL.Proposition Atom), (φ.or ψ) ∈ S → φ ∈ S ∨ ψ ∈ S

/-! ## Prime Exclusion Lemma (Intuitionistic) -/

/-- **Prime Exclusion Lemma for IntDCCS**:
Given an IntDCCS S with phi ∉ S, there exists a prime IntDCCS T ⊇ S with phi ∉ T.

Thin wrapper around `Metalogic.prime_exclusion` with `Cons := PropSetConsistent IntPropAxiom`,
`cl := intDeductiveClosure`, and the EFQ bridge from `phi_mem_cl_of_not_cons`.

See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Lemma 5.5. -/
theorem int_prime_exclusion {S : Set (PL.Proposition Atom)}
    (h_dccs : IntDCCS S) {phi : PL.Proposition Atom}
    (h_not : phi ∉ S) :
    ∃ T : Set (PL.Proposition Atom),
      S ⊆ T ∧ IntPrimeDCCS T ∧ phi ∉ T := by
  -- IntDCCS = Admissible D (PropSetConsistent IntPropAxiom) definitionally
  obtain ⟨T, hST, hprime, hphi⟩ := Metalogic.prime_exclusion
      (propDerivationSystem IntPropAxiom) (PropSetConsistent IntPropAxiom)
      h_dccs h_not
      -- orE schema: (A → χ) → ((B → χ) → ((A ∨ B) → χ))
      (fun A B χ => ⟨.ax [] _ (.orE A B χ)⟩)
      -- deductive closure operator and its laws
      intDeductiveClosure
      int_subset_deductive_closure
      (fun {X ψ} h => h)
      intDeductiveClosure_is_dccs
      -- EFQ bridge: phi ∈ cl X when X is inconsistent
      (fun {X} h_not_cons => by
        simp only [PropSetConsistent, Metalogic.SetConsistent, Metalogic.Consistent,
          not_forall, not_not] at h_not_cons
        obtain ⟨Linc, hLinc_sub, hLinc_bot⟩ := h_not_cons
        let efq : DerivationTree IntPropAxiom (Atom := Atom) []
            ((⊥ : PL.Proposition Atom).imp phi) :=
          .ax [] _ (.efq phi)
        let efq_w := DerivationTree.weakening [] Linc _ efq (fun _ h => nomatch h)
        obtain ⟨d_bot⟩ := hLinc_bot
        let d_phi := DerivationTree.modus_ponens Linc _ _ efq_w d_bot
        exact ⟨Linc, hLinc_sub, ⟨d_phi⟩⟩)
      -- cut witness via int_deriv_imp_of_union
      (fun {U L a b} hL hd =>
        int_deriv_imp_of_union
          (fun x hx => by
            rcases Set.mem_insert_iff.mp (hL x hx) with rfl | hu
            · exact Set.mem_union_right U (Set.mem_singleton_iff.mpr rfl)
            · exact Set.mem_union_left _ hu)
          hd)
      -- Cons preserved by chains: consistency of ⋃₀ C via finite_list_in_chain_member
      (fun C hchain hCne hCsub L hL hd =>
        let ⟨T', hT'C, hLT'⟩ := Metalogic.finite_list_in_chain_member hchain hCne L hL
        (hCsub hT'C).2.1.1 L hLT' hd)
  -- PrimeAdmissible D (PropSetConsistent IntPropAxiom) T = IntPrimeDCCS T definitionally
  exact ⟨T, hST, ⟨hprime.1, hprime.2⟩, hphi⟩

/-! ## Int Theorems Form a DCCS -/

/-- Lift an `IntPropAxiom` derivation tree to a `PropositionalAxiom` derivation tree,
recursing through the tree via `IntPropAxiom.toPropAxiom` on the axiom leaves. -/
private noncomputable def liftIntToCl {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree IntPropAxiom Γ φ) :
    DerivationTree PropositionalAxiom Γ φ := by
  match d with
  | .ax Γ ψ h_ax => exact .ax Γ ψ h_ax.toPropAxiom
  | .assumption Γ ψ h_mem => exact .assumption Γ ψ h_mem
  | .modus_ponens Γ ψ χ d₁ d₂ =>
    exact .modus_ponens Γ ψ χ (liftIntToCl d₁) (liftIntToCl d₂)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact .weakening Γ' Δ ψ (liftIntToCl d') h_sub

/-- IntPropAxiom is consistent: `[] ⊬ ⊥`. -/
theorem int_consistent :
    ¬ Derivable (Atom := Atom) IntPropAxiom (⊥ : PL.Proposition Atom) := by
  intro ⟨d⟩
  have d_cl := liftIntToCl d
  exact prop_soundness d_cl (fun _ => True) (fun _ h => nomatch h)

/-- The set of IntPropAxiom-theorems `{ψ | Derivable IntPropAxiom ψ}` is a DCCS. -/
theorem int_theorems_dccs :
    IntDCCS ({ψ : PL.Proposition Atom | Derivable IntPropAxiom ψ}) := by
  constructor
  · -- Consistent
    intro L hL hd
    have hL_empty : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
        (∀ y ∈ Lx, y ∈ (∅ : Set (PL.Proposition Atom))) ∧
        (propDerivationSystem IntPropAxiom).Deriv Lx x := by
      intro x hx
      obtain ⟨dx⟩ := (hL x hx : Derivable IntPropAxiom x)
      exact ⟨[], fun _ h => (nomatch h), ⟨dx⟩⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
      int_deriv_from_closure_to_S L hL_empty _ hd
    have hL'_nil : L' = [] := by
      by_contra h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L' h
      exact (hL'_sub a ha).elim
    rw [hL'_nil] at hL'_deriv
    exact int_consistent hL'_deriv
  · -- Deductively closed
    intro L φ hL hd
    have hL_empty : ∀ x ∈ L, ∃ Lx : List (PL.Proposition Atom),
        (∀ y ∈ Lx, y ∈ (∅ : Set (PL.Proposition Atom))) ∧
        (propDerivationSystem IntPropAxiom).Deriv Lx x := by
      intro x hx
      obtain ⟨dx⟩ := (hL x hx : Derivable IntPropAxiom x)
      exact ⟨[], fun _ h => (nomatch h), ⟨dx⟩⟩
    obtain ⟨L', hL'_sub, hL'_deriv⟩ :=
      int_deriv_from_closure_to_S L hL_empty _ hd
    have hL'_nil : L' = [] := by
      by_contra h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L' h
      exact (hL'_sub a ha).elim
    rw [hL'_nil] at hL'_deriv
    exact hL'_deriv

end Cslib.Logic.PL
