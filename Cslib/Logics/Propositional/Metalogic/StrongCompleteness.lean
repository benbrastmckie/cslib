/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Bool
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.MCS
public import Cslib.Logics.Propositional.Metalogic.Soundness

/-! # Canonical Model and Strong Completeness for Classical Propositional Logic

This module provides the canonical model (MCS) construction and proves strong soundness
and strong completeness for classical propositional logic. Strong completeness states that
if `φ` is a classical semantic consequence of a set `Γ`, then `φ` is set-derivable from `Γ`.

## Main Results

### Canonical Model Infrastructure

- `canonicalValuation`: The canonical valuation from a maximally consistent set.
- `prop_truth_lemma`: `Evaluate (canonicalValuation S) φ ↔ φ ∈ S` for MCS `S`.

### Strong Soundness and Completeness

- `prop_strong_soundness`: `SetDerivable PropositionalAxiom Γ φ → SemanticEntails Γ φ`
- `prop_strong_completeness`: `SemanticEntails Γ φ → SetDerivable PropositionalAxiom Γ φ`
- `prop_strong_completeness_iff`: `SemanticEntails Γ φ ↔ SetDerivable PropositionalAxiom Γ φ`
- `prop_compactness`: If `φ` is a classical consequence of `Γ`, there is a finite `L ⊆ Γ`
  with the same property.
- `prop_completeness`: `Tautology φ → Derivable PropositionalAxiom φ`
- `prop_completeness_iff_tautology`: `Tautology φ ↔ Derivable PropositionalAxiom φ`

## Strategy

Soundness: unfold `SetDerivable` to get `L ⊆ Γ`, apply `prop_soundness`.

Completeness: by contrapositive. If `φ` is not set-derivable from `Γ`, show `Γ ∪ {¬φ}`
is consistent, apply `prop_lindenbaum` to get an MCS containing `Γ ∪ {¬φ}`, then use
`prop_truth_lemma` to show all of `Γ` is true at the canonical valuation but `φ` is false.

The consistency proof eliminates `¬φ` from any inconsistency witness via `deductionWithMem`,
then applies EFQ + Peirce's law to derive `φ` from `L \ {¬φ} ⊆ Γ`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
* Cslib/Logics/Modal/Metalogic/KCompleteness.lean -- modal K completeness
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open Cslib.Logic.Helpers

universe u

variable {Atom : Type u}

attribute [local instance] Classical.propDecidable

/-! ## Canonical Valuation -/

/-- The canonical valuation from a maximally consistent set.

For MCS `S`, the atom `p` is true iff `Proposition.atom p ∈ S`. -/
def canonicalValuation (S : Set (PL.Proposition Atom)) :
    Valuation Atom :=
  fun p => Proposition.atom p ∈ S

/-! ## Truth Lemma: Per-Connective Helpers -/

/-- **Truth Lemma (atom)**: `Evaluate v (atom p) ↔ atom p ∈ S`. Trivial since
the canonical valuation is defined as `fun p => atom p ∈ S`. -/
theorem prop_truth_lemma_atom
    {S : Set (PL.Proposition Atom)}
    (_h_mcs : PropSetMaximalConsistent PropositionalAxiom S)
    (p : Atom) :
    Evaluate (canonicalValuation S) (.atom p) ↔ (.atom p) ∈ S :=
  Iff.rfl

/-- **Truth Lemma (bot)**: `Evaluate v ⊥ ↔ ⊥ ∈ S`. The forward direction
is vacuously true (⊥ never evaluates to true); the backward direction uses
`prop_mcs_bot_not_mem`. -/
theorem prop_truth_lemma_bot
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S) :
    Evaluate (canonicalValuation S) .bot ↔ (.bot : PL.Proposition Atom) ∈ S := by
  constructor
  · intro h; exact absurd h id
  · intro h; exact absurd h (prop_mcs_bot_not_mem h_mcs)

/-- **Truth Lemma (and)**: Given IH for φ and ψ, prove
`Evaluate v (φ ∧ ψ) ↔ (φ ∧ ψ) ∈ S`. -/
theorem prop_truth_lemma_and
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S)
    (φ ψ : PL.Proposition Atom)
    (ih_φ : Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
    (ih_ψ : Evaluate (canonicalValuation S) ψ ↔ ψ ∈ S) :
    Evaluate (canonicalValuation S) (φ.and ψ) ↔ (φ.and ψ) ∈ S := by
  constructor
  · -- Forward: Evaluate v (φ ∧ ψ) → (φ ∧ ψ) ∈ S
    intro ⟨hφ, hψ⟩
    have h_phi_S := ih_φ.mp hφ
    have h_psi_S := ih_ψ.mp hψ
    apply prop_closed_under_derivation
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
      (L := [φ, ψ])
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        cases hx with
        | inl h => exact h ▸ h_phi_S
        | inr h => exact h ▸ h_psi_S)
    show (propDerivationSystem PropositionalAxiom).Deriv _ _
    unfold propDerivationSystem Deriv
    exact ⟨.modusPonens _ _ _
      (.modusPonens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.andI φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons])))
      (.assumption _ _ (by simp [List.mem_cons]))⟩
  · -- Backward: (φ ∧ ψ) ∈ S → Evaluate v (φ ∧ ψ)
    intro h_mem
    constructor
    · apply ih_φ.mpr
      apply prop_closed_under_derivation
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
        (L := [φ.and ψ])
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem)
      show (propDerivationSystem PropositionalAxiom).Deriv _ _
      unfold propDerivationSystem Deriv
      exact ⟨.modusPonens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.andE1 φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons]))⟩
    · apply ih_ψ.mpr
      apply prop_closed_under_derivation
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
        (L := [φ.and ψ])
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem)
      show (propDerivationSystem PropositionalAxiom).Deriv _ _
      unfold propDerivationSystem Deriv
      exact ⟨.modusPonens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.andE2 φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons]))⟩

/-- **Truth Lemma (or)**: Given IH for φ and ψ, prove
`Evaluate v (φ ∨ ψ) ↔ (φ ∨ ψ) ∈ S`. -/
theorem prop_truth_lemma_or
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S)
    (φ ψ : PL.Proposition Atom)
    (ih_φ : Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
    (ih_ψ : Evaluate (canonicalValuation S) ψ ↔ ψ ∈ S) :
    Evaluate (canonicalValuation S) (φ.or ψ) ↔ (φ.or ψ) ∈ S := by
  constructor
  · -- Forward: Evaluate v (φ ∨ ψ) → (φ ∨ ψ) ∈ S
    intro h_or
    rcases h_or with hφ | hψ
    · have h_phi_S := ih_φ.mp hφ
      apply prop_closed_under_derivation
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
        (L := [φ])
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_phi_S)
      show (propDerivationSystem PropositionalAxiom).Deriv _ _
      unfold propDerivationSystem Deriv
      exact ⟨.modusPonens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.orI1 φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons]))⟩
    · have h_psi_S := ih_ψ.mp hψ
      apply prop_closed_under_derivation
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
        (L := [ψ])
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_psi_S)
      show (propDerivationSystem PropositionalAxiom).Deriv _ _
      unfold propDerivationSystem Deriv
      exact ⟨.modusPonens _ _ _
        (.weakening [] _ _
          (.ax [] _ (.orI2 φ ψ))
          (fun _ h => nomatch h))
        (.assumption _ _ (by simp [List.mem_cons]))⟩
  · -- Backward: (φ ∨ ψ) ∈ S → Evaluate v (φ ∨ ψ)
    intro h_mem
    -- Use negation_complete: either φ ∈ S or ¬φ ∈ S
    rcases prop_negation_complete
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs φ with hφ | hnφ
    · exact Or.inl (ih_φ.mpr hφ)
    · rcases prop_negation_complete
          PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs ψ with hψ | hnψ
      · exact Or.inr (ih_ψ.mpr hψ)
      · -- Both ¬φ ∈ S and ¬ψ ∈ S; derive ⊥ using orE
        exfalso
        apply prop_mcs_bot_not_mem h_mcs
        -- orE: (φ → ⊥) → ((ψ → ⊥) → ((φ ∨ ψ) → ⊥))
        apply prop_closed_under_derivation
            PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
          (L := [φ.imp .bot, ψ.imp .bot, φ.or ψ])
          (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            cases hx with
            | inl h => exact h ▸ hnφ
            | inr h =>
              cases h with
              | inl h => exact h ▸ hnψ
              | inr h => exact h ▸ h_mem)
        show (propDerivationSystem PropositionalAxiom).Deriv _ _
        unfold propDerivationSystem Deriv
        -- [¬φ, ¬ψ, φ ∨ ψ] ⊢ ⊥ via orE axiom + three modus ponens
        exact ⟨.modusPonens _ _ _
          (.modusPonens _ _ _
            (.modusPonens _ _ _
              (.weakening [] _ _
                (.ax [] _ (.orE φ ψ .bot))
                (fun _ h => nomatch h))
              (.assumption _ _ (by simp [List.mem_cons])))
            (.assumption _ _ (by simp [List.mem_cons])))
          (.assumption _ _ (by simp [List.mem_cons]))⟩

/-- **Truth Lemma (imp)**: Given IH for φ and ψ, prove
`Evaluate v (φ → ψ) ↔ (φ → ψ) ∈ S`. -/
theorem prop_truth_lemma_imp
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S)
    (φ ψ : PL.Proposition Atom)
    (ih_φ : Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
    (ih_ψ : Evaluate (canonicalValuation S) ψ ↔ ψ ∈ S) :
    Evaluate (canonicalValuation S) (φ.imp ψ) ↔ (φ.imp ψ) ∈ S := by
  constructor
  · -- Forward: Evaluate v (φ → ψ) → (φ → ψ) ∈ S
    intro h_sat
    rcases prop_negation_complete PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS
      h_mcs (φ → ψ) with h | h
    · exact h
    · exfalso
      -- h : neg (φ.imp ψ) ∈ S
      -- Derive φ ∈ S from neg (φ.imp ψ) ∈ S
      have h_phi_S : φ ∈ S := by
        apply prop_closed_under_derivation
          PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
          (L := [(φ.imp ψ).imp .bot])
          (fun x hx => by
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hx
            exact hx ▸ h)
        show (propDerivationSystem
          PropositionalAxiom).Deriv _ _
        unfold propDerivationSystem Deriv
        -- [(φ→ψ), (φ→ψ)→⊥] ⊢ ⊥
        have d_bot' :
            DerivationTree PropositionalAxiom
            [φ.imp ψ, (φ.imp ψ).imp .bot]
            Proposition.bot :=
          .modusPonens _ (φ.imp ψ) .bot
            (.assumption _ _
              (by simp [List.mem_cons, Proposition.imp_def]))
            (.assumption _ _
              (by simp [List.mem_cons]))
        -- [(φ→ψ), (φ→ψ)→⊥] ⊢ φ (via EFQ)
        have d_efq' :
            DerivationTree PropositionalAxiom
            [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
          .modusPonens _ .bot φ
            (.weakening [] _ _
              (.ax [] _ (.efq φ))
              (fun _ h => nomatch h))
            d_bot'
        -- deduction: [(φ→ψ)→⊥] ⊢ (φ→ψ) → φ
        have d_dt := deductionTheorem
          PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS
          [(φ.imp ψ).imp .bot] (φ.imp ψ) φ
          d_efq'
        -- Peirce: [(φ→ψ)→⊥] ⊢ ((φ→ψ)→φ) → φ
        have d_peirce' :
            DerivationTree PropositionalAxiom
            [(φ.imp ψ).imp .bot]
            (((φ.imp ψ).imp φ).imp φ) :=
          .weakening [] _ _
            (.ax [] _ (.peirce φ ψ))
            (fun _ h => nomatch h)
        -- MP: [(φ→ψ)→⊥] ⊢ φ
        exact ⟨.modusPonens _ _ _
          d_peirce' d_dt⟩
      -- By IH backward, Evaluate v φ
      have h_sat_phi := ih_φ.mpr h_phi_S
      -- By assumption, Evaluate v ψ
      have h_psi_S := ih_ψ.mp (h_sat h_sat_phi)
      -- Derive ¬ψ ∈ S from neg (φ → ψ) ∈ S
      have h_neg_psi_S :
          (¬ψ) ∈ S := by
        apply prop_closed_under_derivation
          PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
          (L := [(φ.imp ψ).imp .bot])
          (fun x hx => by
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hx
            exact hx ▸ h)
        show (propDerivationSystem
          PropositionalAxiom).Deriv _ _
        unfold propDerivationSystem Deriv
        -- [ψ, (φ→ψ)→⊥] ⊢ φ→ψ via implyK
        have d_imp :
            DerivationTree PropositionalAxiom
            [ψ, (φ.imp ψ).imp .bot]
            (φ.imp ψ) :=
          .modusPonens _ ψ (φ.imp ψ)
            (.weakening [] _ _
              (.ax [] _ (.implyK ψ φ))
              (fun _ h => nomatch h))
            (.assumption _ _
              (by simp [List.mem_cons]))
        -- [ψ, (φ→ψ)→⊥] ⊢ ⊥
        have d_bot'' :
            DerivationTree PropositionalAxiom
            [ψ, (φ.imp ψ).imp .bot]
            Proposition.bot :=
          .modusPonens _ (φ.imp ψ) .bot
            (.assumption _ _
              (by simp [List.mem_cons, Proposition.imp_def]))
            d_imp
        -- deduction: [(φ→ψ)→⊥] ⊢ ψ → ⊥
        exact ⟨deductionTheorem
          PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS
          [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
      -- Contradiction: ψ ∈ S and ¬ψ ∈ S
      exact prop_mcs_bot_not_mem h_mcs
        (prop_implication_property
          PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs
          h_neg_psi_S h_psi_S)
  · -- Backward: (φ → ψ) ∈ S → Evaluate v φ → Evaluate v ψ
    intro h_mem h_sat_phi
    exact ih_ψ.mpr
      (prop_implication_property
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS h_mcs h_mem
        (ih_φ.mp h_sat_phi))

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For an MCS `S` and its canonical valuation `v`,
`Evaluate v φ ↔ φ ∈ S`.

Proof by structural recursion on `φ`, dispatching to per-connective helpers:
`prop_truth_lemma_atom`, `prop_truth_lemma_bot`, `prop_truth_lemma_and`,
`prop_truth_lemma_or`, `prop_truth_lemma_imp`. -/
theorem prop_truth_lemma
    {S : Set (PL.Proposition Atom)}
    (h_mcs : PropSetMaximalConsistent PropositionalAxiom S) :
    (φ : PL.Proposition Atom) →
    (Evaluate (canonicalValuation S) φ ↔ φ ∈ S)
  | .atom p => prop_truth_lemma_atom h_mcs p
  | .bot => prop_truth_lemma_bot h_mcs
  | .and φ ψ =>
    prop_truth_lemma_and h_mcs φ ψ
      (prop_truth_lemma h_mcs φ) (prop_truth_lemma h_mcs ψ)
  | .or φ ψ =>
    prop_truth_lemma_or h_mcs φ ψ
      (prop_truth_lemma h_mcs φ) (prop_truth_lemma h_mcs ψ)
  | .imp φ ψ =>
    prop_truth_lemma_imp h_mcs φ ψ
      (prop_truth_lemma h_mcs φ) (prop_truth_lemma h_mcs ψ)

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

/-! ## Helper: Double-Negation Elimination via EFQ + Peirce -/

/-- Given a derivation `ctx ⊢ ¬φ → ⊥` (i.e., `ctx ⊢ (φ → ⊥) → ⊥`), produce
`ctx ⊢ φ` via EFQ + implyS composition + Peirce's law. -/
private noncomputable def dne_from_neg_neg
    {Atom : Type*} {φ : PL.Proposition Atom}
    {ctx : List (PL.Proposition Atom)}
    (d_neg_neg : DerivationTree PropositionalAxiom ctx ((¬φ).imp Proposition.bot)) :
    DerivationTree PropositionalAxiom ctx φ :=
  -- EFQ: ctx ⊢ ⊥ → φ
  let d_efq : DerivationTree PropositionalAxiom ctx (Proposition.bot.imp φ) :=
    .weakening [] ctx _ (.ax [] _ (.efq φ)) (fun _ h => nomatch h)
  -- implyK: ctx ⊢ (⊥ → φ) → (¬φ → (⊥ → φ))
  let d_k : DerivationTree PropositionalAxiom ctx
      ((Proposition.bot.imp φ).imp ((¬φ).imp (Proposition.bot.imp φ))) :=
    .weakening [] ctx _ (.ax [] _ (.implyK (Proposition.bot.imp φ) (¬φ)))
      (fun _ h => nomatch h)
  -- Combine: ctx ⊢ ¬φ → (⊥ → φ)
  let d_step2 := DerivationTree.modusPonens ctx _ _ d_k d_efq
  -- implyS: ctx ⊢ (¬φ → (⊥ → φ)) → ((¬φ → ⊥) → (¬φ → φ))
  let d_s2 : DerivationTree PropositionalAxiom ctx
      (((¬φ).imp (Proposition.bot.imp φ)).imp
        (((¬φ).imp Proposition.bot).imp ((¬φ).imp φ))) :=
    .weakening [] ctx _ (.ax [] _ (.implyS (¬φ) Proposition.bot φ))
      (fun _ h => nomatch h)
  -- ctx ⊢ (¬φ → ⊥) → (¬φ → φ)
  let d_step3 := DerivationTree.modusPonens ctx _ _ d_s2 d_step2
  -- ctx ⊢ ¬φ → φ
  let d_neg_to_phi : DerivationTree PropositionalAxiom ctx ((¬φ).imp φ) :=
    DerivationTree.modusPonens ctx _ _ d_step3 d_neg_neg
  -- Peirce: ctx ⊢ (¬φ → φ) → φ
  let d_peirce : DerivationTree PropositionalAxiom ctx (((¬φ).imp φ).imp φ) :=
    .weakening [] ctx _ (.ax [] _ (.peirce φ Proposition.bot)) (fun _ h => nomatch h)
  -- ctx ⊢ φ
  DerivationTree.modusPonens ctx _ _ d_peirce d_neg_to_phi

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
    have d_neg_neg := deductionWithMem
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS L (¬φ)
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
    -- DNE: ctx ⊢ ¬φ → ⊥ gives ctx ⊢ φ via EFQ + Peirce
    exact h_not ⟨ctx, h_rem_sub, ⟨dne_from_neg_neg d_neg_neg⟩⟩
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
    have d_dt := deductionTheorem
        PropositionalAxiom.mem_implyK PropositionalAxiom.mem_implyS L (¬φ) Proposition.bot d_ext
    -- d_dt : L ⊢ ¬φ → ⊥ (even though ¬φ wasn't in L)
    -- DNE: L ⊢ ¬φ → ⊥ gives L ⊢ φ via EFQ + Peirce
    exact h_not ⟨L, hL_Γ, ⟨dne_from_neg_neg d_dt⟩⟩

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
@[simp]
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
  exact ⟨L, hL_sub, prop_strong_soundness ⟨L, fun x hx => Set.mem_ofPred_eq.mpr hx, hL_deriv⟩⟩

/-! ## Weak Completeness Corollary -/

/-- **Weak Completeness for Classical Propositional Logic**:
If `φ` is a tautology (true under all valuations), then `φ` is derivable using
`PropositionalAxiom`.

This is a corollary of `prop_strong_completeness`: a tautology is a semantic consequence
of the empty set, so strong completeness gives set-derivability from `∅`, and
`SetDerivable_empty_iff` converts this to ordinary derivability. -/
theorem prop_completeness {φ : PL.Proposition Atom}
    (h_taut : Tautology φ) : Derivable PropositionalAxiom φ :=
  SetDerivable_empty_iff.mp
    (prop_strong_completeness (SemanticEntails_of_Tautology h_taut ∅))

/-- **Soundness and Completeness**: `φ` is a tautology iff `φ` is derivable
from the empty context using `PropositionalAxiom`.

This is a corollary of `prop_strong_completeness_iff` obtained by instantiating at
`Γ = ∅` and using `SetDerivable_empty_iff`. -/
@[simp] theorem prop_completeness_iff_tautology {φ : PL.Proposition Atom} :
    Tautology φ ↔ Derivable PropositionalAxiom φ :=
  ⟨prop_completeness, prop_soundness_tautology⟩

/-- Derivability from `PropositionalAxiom` is decidable when `Atom` is a `Fintype` with
`DecidableEq`. The decision procedure reduces derivability to tautology-checking via
`prop_completeness_iff_tautology`, then uses `instDecidableTautology` to enumerate all
Boolean valuations. -/
instance instDecidableDerivablePropositionalAxiom [Fintype Atom] [DecidableEq Atom]
    (phi : PL.Proposition Atom) : Decidable (Derivable PropositionalAxiom phi) :=
  decidable_of_iff (Tautology phi) prop_completeness_iff_tautology

end Cslib.Logic.PL
