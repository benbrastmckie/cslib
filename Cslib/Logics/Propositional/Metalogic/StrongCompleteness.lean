/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.Completeness

/-! # Strong Completeness for Classical Propositional Logic

This module proves strong soundness and strong completeness for classical propositional logic
via the canonical valuation (MCS) construction. Strong completeness states that if `φ` is a
classical semantic consequence of a set `Γ`, then `φ` is set-derivable from `Γ`.

## Main Results

- `prop_strong_soundness`: `SetDerivable PropositionalAxiom Γ φ → SemanticEntails Γ φ`
- `prop_strong_completeness`: `SemanticEntails Γ φ → SetDerivable PropositionalAxiom Γ φ`
- `prop_strong_completeness_iff`: `SemanticEntails Γ φ ↔ SetDerivable PropositionalAxiom Γ φ`
- `prop_compactness`: If `φ` is a classical consequence of `Γ`, there is a finite `L ⊆ Γ`
  with the same property.

## Strategy

Soundness: unfold `SetDerivable` to get `L ⊆ Γ`, apply `prop_soundness`.

Completeness: by contrapositive. If `φ` is not set-derivable from `Γ`, show `Γ ∪ {¬φ}`
is consistent, apply `prop_lindenbaum` to get an MCS containing `Γ ∪ {¬φ}`, then use
`prop_truth_lemma` to show all of `Γ` is true at the canonical valuation but `φ` is false.

The consistency proof eliminates `¬φ` from any inconsistency witness via `deductionWithMem`,
then applies EFQ + Peirce's law to derive `φ` from `L \ {¬φ} ⊆ Γ`.

## References

* CZ Theorem 1.16 (classical compactness)
* Cslib/Logics/Propositional/Metalogic/Completeness.lean
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Helpers

universe u

variable {Atom : Type u}

attribute [local instance] Classical.propDecidable

/-! ## Axiom hypotheses for PropositionalAxiom -/

private def sc_h_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    PropositionalAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

private def sc_h_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    PropositionalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

/-! ## Strong Soundness -/

/-- **Strong Soundness for Classical Logic**:
If `φ` is set-derivable from `Γ` using `PropositionalAxiom`, then `φ` is a classical
semantic consequence of `Γ`. -/
theorem prop_strong_soundness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : SetDerivable PropositionalAxiom Γ φ) : SemanticEntails Γ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  intro v h_sat
  exact prop_soundness d v (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## Key Lemma: Consistency of Γ ∪ {¬φ} -/

/-- If `φ` is not set-derivable from `Γ`, then `Γ ∪ {¬φ}` is
`PropSetConsistent PropositionalAxiom`.

Proof: by contradiction. If some finite `L ⊆ Γ ∪ {¬φ}` derives `⊥`, use
`deductionWithMem` to eliminate `¬φ` from `L` and get `L' ⊆ Γ` with `L' ⊢ ¬φ → ⊥`.
Then EFQ + Peirce gives `L' ⊢ φ`, contradicting `¬ SetDerivable PropositionalAxiom Γ φ`. -/
theorem prop_not_SetDerivable_union_neg_consistent
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h_not : ¬ SetDerivable PropositionalAxiom Γ φ) :
    PropSetConsistent PropositionalAxiom (Γ ∪ {(¬φ)}) := by
  intro L hL hL_bot
  obtain ⟨d_bot⟩ := hL_bot
  -- Case split: is ¬φ in L?
  by_cases h_neg_in_L : (¬φ) ∈ L
  · -- ¬φ ∈ L: use deductionWithMem to eliminate ¬φ from L
    -- deductionWithMem: removeAll L (¬φ) ⊢ ¬φ → ⊥
    have d_neg_neg := deductionWithMem sc_h_implyK sc_h_implyS L (¬φ)
        Proposition.bot d_bot h_neg_in_L
    -- removeAll L (¬φ) ⊆ Γ
    have h_rem_sub : ∀ x ∈ removeAll L (¬φ), x ∈ Γ := by
      intro x hx
      simp only [removeAll, ne_eq, decide_not, List.mem_filter,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hx
      obtain ⟨hx_in, hx_ne⟩ := hx
      rcases hL x hx_in with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hx_ne
    let ctx := removeAll L (¬φ)
    -- EFQ + S: ctx ⊢ ¬φ → ⊥ and ctx ⊢ ⊥ → φ, so ctx ⊢ ¬φ → φ
    have d_efq : DerivationTree PropositionalAxiom (Atom := Atom) ctx
        (Proposition.bot.imp φ) :=
      .weakening [] ctx _ (.ax [] _ (.efq φ)) (fun _ h => nomatch h)
    have d_k : DerivationTree PropositionalAxiom (Atom := Atom) ctx
        ((Proposition.bot.imp φ).imp ((¬φ).imp (Proposition.bot.imp φ))) :=
      .weakening [] ctx _ (.ax [] _ (.implyK (Proposition.bot.imp φ) (¬φ)))
        (fun _ h => nomatch h)
    have d_step2 := DerivationTree.modus_ponens ctx _ _ d_k d_efq
    have d_s2 : DerivationTree PropositionalAxiom (Atom := Atom) ctx
        (((¬φ).imp (Proposition.bot.imp φ)).imp
          (((¬φ).imp Proposition.bot).imp ((¬φ).imp φ))) :=
      .weakening [] ctx _ (.ax [] _ (.implyS (¬φ) Proposition.bot φ))
        (fun _ h => nomatch h)
    have d_step3 := DerivationTree.modus_ponens ctx _ _ d_s2 d_step2
    have d_neg_to_phi : DerivationTree PropositionalAxiom (Atom := Atom) ctx ((¬φ).imp φ) :=
      DerivationTree.modus_ponens ctx _ _ d_step3 d_neg_neg
    -- Peirce: (¬φ → φ) → φ
    have d_peirce : DerivationTree PropositionalAxiom (Atom := Atom) ctx (((¬φ).imp φ).imp φ) :=
      .weakening [] ctx _ (.ax [] _ (.peirce φ Proposition.bot)) (fun _ h => nomatch h)
    have d_phi : DerivationTree PropositionalAxiom (Atom := Atom) ctx φ :=
      DerivationTree.modus_ponens ctx _ _ d_peirce d_neg_to_phi
    exact h_not ⟨ctx, h_rem_sub, ⟨d_phi⟩⟩
  · -- ¬φ ∉ L: all elements of L are already in Γ
    have hL_Γ : ∀ x ∈ L, x ∈ Γ := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hx) h_neg_in_L
    -- Same DNE argument, but directly with L ⊆ Γ
    -- From d_bot : L ⊢ ⊥ and DT: [] ⊢ ¬φ → ⊥? No, we don't have ¬φ in L.
    -- Wait: L derives ⊥ (from Γ), but ¬φ ∉ L.
    -- Apply deduction theorem on ¬φ:
    have d_ext : DerivationTree PropositionalAxiom ((¬φ) :: L) Proposition.bot :=
      .weakening L ((¬φ) :: L) _ d_bot (fun x hx => List.mem_cons.mpr (Or.inr hx))
    have d_dt := deductionTheorem sc_h_implyK sc_h_implyS L (¬φ) Proposition.bot d_ext
    -- d_dt : L ⊢ ¬φ → ⊥ (even though ¬φ wasn't in L)
    -- EFQ: ⊥ → φ
    have d_efq : DerivationTree PropositionalAxiom (Atom := Atom) L
        (Proposition.bot.imp φ) :=
      .weakening [] L _ (.ax [] _ (.efq φ)) (fun _ h => nomatch h)
    have d_k : DerivationTree PropositionalAxiom (Atom := Atom) L
        ((Proposition.bot.imp φ).imp ((¬φ).imp (Proposition.bot.imp φ))) :=
      .weakening [] L _ (.ax [] _ (.implyK (Proposition.bot.imp φ) (¬φ)))
        (fun _ h => nomatch h)
    have d_step2 := DerivationTree.modus_ponens L _ _ d_k d_efq
    have d_s2 : DerivationTree PropositionalAxiom (Atom := Atom) L
        (((¬φ).imp (Proposition.bot.imp φ)).imp
          (((¬φ).imp Proposition.bot).imp ((¬φ).imp φ))) :=
      .weakening [] L _ (.ax [] _ (.implyS (¬φ) Proposition.bot φ))
        (fun _ h => nomatch h)
    have d_step3 := DerivationTree.modus_ponens L _ _ d_s2 d_step2
    have d_neg_to_phi : DerivationTree PropositionalAxiom (Atom := Atom) L ((¬φ).imp φ) :=
      DerivationTree.modus_ponens L _ _ d_step3 d_dt
    have d_peirce : DerivationTree PropositionalAxiom (Atom := Atom) L (((¬φ).imp φ).imp φ) :=
      .weakening [] L _ (.ax [] _ (.peirce φ Proposition.bot)) (fun _ h => nomatch h)
    have d_phi : DerivationTree PropositionalAxiom (Atom := Atom) L φ :=
      DerivationTree.modus_ponens L _ _ d_peirce d_neg_to_phi
    exact h_not ⟨L, hL_Γ, ⟨d_phi⟩⟩

/-! ## Strong Completeness -/

/-- **Strong Completeness for Classical Logic**:
If `φ` is a classical semantic consequence of `Γ`, then `φ` is set-derivable from `Γ`
using `PropositionalAxiom`.

Proof by contrapositive: assume `φ` is not set-derivable from `Γ`. Then by
`prop_not_SetDerivable_union_neg_consistent`, `Γ ∪ {¬φ}` is consistent. Apply
`prop_lindenbaum` to extend to an MCS `M`. By `prop_truth_lemma`, the canonical valuation
from `M` satisfies all of `Γ` (since `Γ ⊆ M`) but falsifies `φ` (since `¬φ ∈ M`). -/
theorem prop_strong_completeness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : SemanticEntails Γ φ) : SetDerivable PropositionalAxiom Γ φ := by
  by_contra h_not
  -- Γ ∪ {¬φ} is consistent
  have h_cons := prop_not_SetDerivable_union_neg_consistent h_not
  -- Extend to MCS M ⊇ Γ ∪ {¬φ}
  obtain ⟨M, hM_sup, hM_mcs⟩ := prop_lindenbaum h_cons
  -- ¬φ ∈ M
  have h_neg_phi : (¬φ) ∈ M :=
    hM_sup (Set.mem_union_right Γ (Set.mem_singleton_iff.mpr rfl))
  -- All of Γ ⊆ M
  have h_gamma_sub : ∀ ψ ∈ Γ, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left {¬φ} hψ)
  -- The canonical valuation satisfies all of Γ
  have h_gamma_val : ∀ ψ ∈ Γ, Evaluate (canonicalValuation M) ψ :=
    fun ψ hψ => (prop_truth_lemma hM_mcs ψ).mpr (h_gamma_sub ψ hψ)
  -- By SemanticEntails: Evaluate v φ
  have h_phi_val : Evaluate (canonicalValuation M) φ :=
    h (canonicalValuation M) h_gamma_val
  -- ¬φ ∈ M implies Evaluate v (¬φ), which contradicts Evaluate v φ
  have h_neg_val : Evaluate (canonicalValuation M) (¬φ) :=
    (prop_truth_lemma hM_mcs (¬φ)).mpr h_neg_phi
  exact h_neg_val h_phi_val

/-! ## Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for Classical Logic**:
`φ` is a classical semantic consequence of `Γ` iff `φ` is set-derivable from `Γ`. -/
theorem prop_strong_completeness_iff {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    SemanticEntails Γ φ ↔ SetDerivable PropositionalAxiom Γ φ :=
  ⟨prop_strong_completeness, prop_strong_soundness⟩

/-! ## Compactness Corollary -/

/-- **Compactness for Classical Semantics**:
If `φ` is a classical semantic consequence of `Γ`, there is a finite list `L ⊆ Γ`
such that `φ` is a classical semantic consequence of `L`.

Proof: strong completeness gives a finite derivation witness from `Γ`; strong soundness
lifts it back to semantic entailment over just the finite list. -/
theorem prop_compactness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : SemanticEntails Γ φ) :
    ∃ L : List (PL.Proposition Atom),
      (∀ x ∈ L, x ∈ Γ) ∧
      SemanticEntails {ψ | ψ ∈ L} φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := prop_strong_completeness h
  exact ⟨L, hL_sub, prop_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩⟩

end Cslib.Logic.PL
