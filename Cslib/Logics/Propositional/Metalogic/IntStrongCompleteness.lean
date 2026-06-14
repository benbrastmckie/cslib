/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.IntLindenbaum
public import Cslib.Logics.Propositional.Metalogic.IntSoundness

/-! # Canonical Model and Strong Completeness for Intuitionistic Propositional Logic

This module provides the canonical Kripke model construction (prime DCCS worlds) and proves
strong soundness and strong completeness for intuitionistic propositional logic. Strong
completeness states that if `φ` is an intuitionistic Kripke semantic consequence of `Γ`,
then `φ` is set-derivable from `Γ`.

## Main Results

### Canonical Model Infrastructure

- `IntCanonicalWorld`: Canonical world type (prime DCCS for IntPropAxiom)
- `int_truth_lemma`: `IForces v bf S φ ↔ φ ∈ S.val` for canonical worlds

### Strong Soundness and Completeness

- `int_strong_soundness`: `SetDerivable IntPropAxiom Γ φ → ISemanticEntails Γ φ`
- `int_strong_completeness`: `ISemanticEntails Γ φ → SetDerivable IntPropAxiom Γ φ`
- `int_strong_completeness_iff`: `ISemanticEntails Γ φ ↔ SetDerivable IntPropAxiom Γ φ`
- `int_compactness`: If `φ` is an intuitionistic consequence of `Γ`, there is a finite `L ⊆ Γ`
  with the same property.
- `int_completeness`: `IValid φ → Derivable IntPropAxiom φ`
- `int_soundness_completeness`: `IValid φ ↔ Derivable IntPropAxiom φ`

## Strategy

Soundness: unfold `SetDerivable` to get a witness list `L ⊆ Γ`, apply `int_soundness`.

Completeness: by contrapositive. If `φ` is not set-derivable from `Γ`, we show it's not an
intuitionistic consequence either.

Case split on `PropSetConsistent IntPropAxiom (intDeductiveClosure Γ)`:
- **Inconsistent**: `⊥ ∈ intDeductiveClosure Γ`, so `⊥` is set-derivable from `Γ`. By EFQ
  (`IntPropAxiom` includes `.efq`), `φ` is also set-derivable from `Γ`. Contradiction.
- **Consistent**: `intDeductiveClosure Γ` is an `IntDCCS` with `φ ∉ intDeductiveClosure Γ`
  (since φ is not set-derivable). By `int_prime_exclusion`, get a prime IntDCCS `T ⊇ Γ`
  excluding `φ`. The canonical world from `T` satisfies all of `Γ` but not `φ`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Canonical Model -/

/-- A canonical world for intuitionistic logic is a prime DCCS for IntPropAxiom.
Worlds are prime to support the or-backward direction of the truth lemma:
if (φ ∨ ψ) ∈ S then φ ∈ S or ψ ∈ S. -/
def IntCanonicalWorld (Atom : Type*) :=
  { S : Set (PL.Proposition Atom) // IntPrimeDCCS S }

/-- The canonical preorder on IntCanonicalWorld: set inclusion. -/
instance : Preorder (IntCanonicalWorld Atom) where
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/-- The canonical valuation: atom `p` is true at world `S` iff `atom p ∈ S`. -/
def intCanonicalVal (w : IntCanonicalWorld Atom) (p : Atom) : Prop :=
  Proposition.atom p ∈ w.val

/-- The canonical valuation is upward-closed. -/
theorem intCanonicalVal_upward_closed
    {w w' : IntCanonicalWorld Atom} (p : Atom)
    (hw : w ≤ w') (hv : intCanonicalVal w p) : intCanonicalVal w' p :=
  hw hv

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For any canonical world `S` and formula `φ`,
`IForces intCanonicalVal (fun _ => False) S φ ↔ φ ∈ S.val`.

Proof by structural induction on `φ` (3 cases: atom, bot, imp). -/
theorem int_truth_lemma
    (S : IntCanonicalWorld Atom) :
    (φ : PL.Proposition Atom) →
    (IForces intCanonicalVal (fun _ => False) S φ ↔ φ ∈ S.val)
  | .atom p => Iff.rfl
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h; exact absurd h (int_dccs_bot_not_mem S.property.1)
  | .and φ ψ => by
    constructor
    · -- Forward: IForces S (φ ∧ ψ) → (φ ∧ ψ) ∈ S.val
      intro ⟨hφ, hψ⟩
      have h_phi_S := (int_truth_lemma S φ).mp hφ
      have h_psi_S := (int_truth_lemma S ψ).mp hψ
      -- Use andI derivation to conclude φ ∧ ψ ∈ S
      apply S.property.1.2 [φ, ψ] (φ.and ψ)
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        cases hx with
        | inl h => exact h ▸ h_phi_S
        | inr h => exact h ▸ h_psi_S
      · show (propDerivationSystem IntPropAxiom).Deriv _ _
        unfold propDerivationSystem Deriv
        exact ⟨.modus_ponens _ _ _
          (.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.andI φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons])))
          (.assumption _ _ (by simp [List.mem_cons]))⟩
    · -- Backward: (φ ∧ ψ) ∈ S.val → IForces S (φ ∧ ψ)
      intro h_mem
      constructor
      · apply (int_truth_lemma S φ).mpr
        apply S.property.1.2 [φ.and ψ] φ
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem
        · show (propDerivationSystem IntPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.andE1 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
      · apply (int_truth_lemma S ψ).mpr
        apply S.property.1.2 [φ.and ψ] ψ
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem
        · show (propDerivationSystem IntPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.andE2 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
  | .or φ ψ => by
    constructor
    · -- Forward: IForces S (φ ∨ ψ) → (φ ∨ ψ) ∈ S.val
      intro h_or
      rcases h_or with hφ | hψ
      · have h_phi_S := (int_truth_lemma S φ).mp hφ
        apply S.property.1.2 [φ] (φ.or ψ)
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_phi_S
        · show (propDerivationSystem IntPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.orI1 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
      · have h_psi_S := (int_truth_lemma S ψ).mp hψ
        apply S.property.1.2 [ψ] (φ.or ψ)
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_psi_S
        · show (propDerivationSystem IntPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.orI2 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
    · -- Backward: (φ ∨ ψ) ∈ S.val → IForces S (φ ∨ ψ)
      -- Use the disjunction property of prime DCCS worlds:
      -- (φ ∨ ψ) ∈ S → φ ∈ S ∨ ψ ∈ S.
      intro h_mem
      rcases S.property.2 φ ψ h_mem with h | h
      · exact Or.inl ((int_truth_lemma S φ).mpr h)
      · exact Or.inr ((int_truth_lemma S ψ).mpr h)
  | .imp φ ψ => by
    constructor
    · -- Forward: IForces S (φ → ψ) → (φ → ψ) ∈ S.val
      intro h_forces
      by_contra h_not_mem
      -- Get an IntDCCS T' with S ⊆ T', φ ∈ T', ψ ∉ T' (using int_imp_witness)
      obtain ⟨T'_set, hST', hT'_dccs, hφT', hψT'⟩ :=
        int_imp_witness S.property.1 h_not_mem
      -- Extend T' to a prime IntDCCS T that still excludes ψ
      obtain ⟨T_set, hT'T, hT_prime, hψT⟩ :=
        int_prime_exclusion hT'_dccs hψT'
      let T : IntCanonicalWorld Atom := ⟨T_set, hT_prime⟩
      have hle : S ≤ T := Set.Subset.trans hST' hT'T
      have hφT : φ ∈ T.val := hT'T hφT'
      have hf_φ := (int_truth_lemma T φ).mpr hφT
      have hf_ψ := h_forces T hle hf_φ
      exact hψT ((int_truth_lemma T ψ).mp hf_ψ)
    · -- Backward: (φ → ψ) ∈ S.val → IForces S (φ → ψ)
      intro h_mem T hle hf_φ
      have h_imp_T : (φ → ψ) ∈ T.val := hle h_mem
      have h_φ_T : φ ∈ T.val := (int_truth_lemma T φ).mp hf_φ
      have h_ψ_T : ψ ∈ T.val := int_dccs_imp_property T.property.1 h_imp_T h_φ_T
      exact (int_truth_lemma T ψ).mpr h_ψ_T

/-! ## Strong Soundness -/

/-- **Strong Soundness for Intuitionistic Logic**:
If `φ` is set-derivable from `Γ` using `IntPropAxiom`, then `φ` is an intuitionistic
Kripke semantic consequence of `Γ`. -/
theorem int_strong_soundness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : SetDerivable IntPropAxiom Γ φ) : ISemanticEntails Γ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  intro World _ val v_uc w h_sat
  exact int_soundness d val v_uc w
    (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## Helper: SetDerivable and intDeductiveClosure -/

/-- `φ ∈ intDeductiveClosure(Γ)` iff `φ` is set-derivable from `Γ`. -/
theorem intDeductiveClosure_iff_SetDerivable
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    φ ∈ intDeductiveClosure Γ ↔ SetDerivable IntPropAxiom Γ φ := Iff.rfl

/-! ## EFQ Helper -/

/-- If `⊥` is set-derivable from `Γ` using `IntPropAxiom`, then any `φ` is set-derivable
from `Γ` (by EFQ). -/
theorem SetDerivable_efq_int {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h_bot : SetDerivable IntPropAxiom Γ (⊥ : PL.Proposition Atom)) :
    SetDerivable IntPropAxiom Γ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h_bot
  obtain ⟨d_bot⟩ := hL_deriv
  -- Build L ⊢ φ using EFQ: ⊢ ⊥ → φ, then MP
  let efq : DerivationTree IntPropAxiom (Atom := Atom) L (Proposition.bot.imp φ) :=
    .weakening [] L _ (.ax [] _ (.efq φ)) (fun _ h => nomatch h)
  exact ⟨L, hL_sub, ⟨.modus_ponens L (Proposition.bot) φ efq d_bot⟩⟩

/-! ## Strong Completeness -/

/-- **Strong Completeness for Intuitionistic Logic**:
If `φ` is an intuitionistic Kripke semantic consequence of `Γ`, then `φ` is set-derivable
from `Γ` using `IntPropAxiom`.

Proof by contrapositive via canonical model, with an EFQ case split. -/
theorem int_strong_completeness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : ISemanticEntails Γ φ) : SetDerivable IntPropAxiom Γ φ := by
  by_contra h_not
  -- φ ∉ intDeductiveClosure(Γ)
  have h_not_mem : φ ∉ intDeductiveClosure Γ :=
    intDeductiveClosure_iff_SetDerivable.not.mpr h_not
  -- Case split on consistency of intDeductiveClosure(Γ)
  by_cases h_cons : PropSetConsistent IntPropAxiom (intDeductiveClosure Γ)
  · -- Consistent case: intDeductiveClosure(Γ) is an IntDCCS
    have h_dccs : IntDCCS (intDeductiveClosure Γ) :=
      ⟨h_cons, fun L φ' hL hd => intDeductiveClosure_dccs_closed Γ L φ' hL hd⟩
    -- By int_prime_exclusion, get a prime IntDCCS T ⊇ intDeductiveClosure(Γ) with φ ∉ T
    obtain ⟨T_set, hT_sup, hT_prime, hT_excl⟩ :=
      int_prime_exclusion h_dccs h_not_mem
    -- Build the canonical world W₀ from T
    let W₀ : IntCanonicalWorld Atom := ⟨T_set, hT_prime⟩
    -- φ is not forced at W₀
    have h_not_forced : ¬ IForces intCanonicalVal (fun _ => False) W₀ φ := by
      intro h_f
      exact hT_excl ((int_truth_lemma W₀ φ).mp h_f)
    -- All members of Γ are in T (since Γ ⊆ intDeductiveClosure(Γ) ⊆ T)
    have h_gamma_sub_T : ∀ ψ ∈ Γ, ψ ∈ T_set := by
      intro ψ hψ
      exact hT_sup (int_subset_deductive_closure Γ hψ)
    -- All members of Γ are forced at W₀
    have h_gamma_forced : ∀ ψ ∈ Γ, IForces intCanonicalVal (fun _ => False) W₀ ψ := by
      intro ψ hψ
      exact (int_truth_lemma W₀ ψ).mpr (h_gamma_sub_T ψ hψ)
    -- Instantiate ISemanticEntails
    have h_forced : IForces intCanonicalVal (fun _ => False) W₀ φ :=
      h (IntCanonicalWorld Atom) intCanonicalVal
        (fun {_ _} p hw hv => intCanonicalVal_upward_closed p hw hv)
        W₀ h_gamma_forced
    exact h_not_forced h_forced
  · -- Inconsistent case: ⊥ is set-derivable from Γ
    -- The inconsistency means some finite list from intDeductiveClosure(Γ) derives ⊥
    simp only [PropSetConsistent, Metalogic.SetConsistent, Metalogic.Consistent,
      not_forall, not_not] at h_cons
    obtain ⟨L_inc, hL_inc_sub, hL_inc_bot⟩ := h_cons
    -- Each element of L_inc is in intDeductiveClosure(Γ), i.e., set-derivable from Γ
    -- So ⊥ is set-derivable from Γ
    have h_bot_sd : SetDerivable IntPropAxiom Γ (⊥ : PL.Proposition Atom) :=
      int_deriv_from_closure_to_S L_inc (fun x hx => hL_inc_sub x hx) _ hL_inc_bot
    -- By EFQ, φ is set-derivable from Γ -- contradiction
    exact h_not (SetDerivable_efq_int h_bot_sd)

/-! ## Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for Intuitionistic Logic**:
`φ` is an intuitionistic Kripke semantic consequence of `Γ` iff `φ` is set-derivable from `Γ`. -/
@[simp]
theorem int_strong_completeness_iff {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    ISemanticEntails Γ φ ↔ SetDerivable IntPropAxiom Γ φ :=
  ⟨int_strong_completeness, int_strong_soundness⟩

/-! ## Compactness Corollary -/

/-- **Compactness for Intuitionistic Kripke Semantics**:
If `φ` is an intuitionistic Kripke semantic consequence of `Γ`, there is a finite
list `L ⊆ Γ` such that `φ` is an intuitionistic Kripke semantic consequence of `L`.

Proof: strong completeness gives a finite derivation witness from `Γ`; strong soundness
lifts it back to semantic entailment over just the finite list. -/
theorem int_compactness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : ISemanticEntails Γ φ) :
    ∃ L : List (PL.Proposition Atom),
      (∀ x ∈ L, x ∈ Γ) ∧
      ISemanticEntails {ψ | ψ ∈ L} φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := int_strong_completeness h
  exact ⟨L, hL_sub, int_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩⟩

/-! ## Weak Completeness Corollary -/

/-- **Weak Completeness for Intuitionistic Propositional Logic**:
If `φ` is intuitionistically valid (forced at every world of every intuitionistic
Kripke model), then `φ` is derivable from the empty context using `IntPropAxiom`.

This is a corollary of `int_strong_completeness`: an intuitionistically valid formula
is an intuitionistic semantic consequence of the empty set, so strong completeness
gives set-derivability from `∅`, and `SetDerivable_empty_iff` converts this to
ordinary derivability. -/
theorem int_completeness {φ : PL.Proposition Atom}
    (h_valid : IValid.{u, u} φ) : Derivable IntPropAxiom φ :=
  SetDerivable_empty_iff.mp
    (int_strong_completeness (ISemanticEntails_of_IValid h_valid ∅))

/-- **Soundness and Completeness for Intuitionistic Logic**:
`φ` is intuitionistically valid iff `φ` is derivable from the empty context
using `IntPropAxiom`.

This is a corollary of `int_strong_completeness_iff` obtained by instantiating at
`Γ = ∅` and using `SetDerivable_empty_iff`. -/
@[simp] theorem int_soundness_completeness {φ : PL.Proposition Atom} :
    IValid.{u, u} φ ↔ Derivable IntPropAxiom φ :=
  ⟨int_completeness, int_soundness_derivable⟩

end Cslib.Logic.PL
