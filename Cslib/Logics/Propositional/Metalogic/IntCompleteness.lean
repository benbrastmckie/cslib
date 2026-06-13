/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Metalogic.IntSoundness
public import Cslib.Logics.Propositional.Metalogic.IntLindenbaum

/-! # Canonical Model Infrastructure for Intuitionistic Propositional Logic

This module provides the canonical Kripke model construction (prime DCCS worlds) used
in the completeness proof for intuitionistic propositional logic. The main completeness
theorems are derived as corollaries of the strong completeness results in
`IntStrongCompleteness.lean`.

## Main Results

- `IntCanonicalWorld`: Canonical world type (prime DCCS for IntPropAxiom)
- `int_truth_lemma`: `IForces v bf S φ ↔ φ ∈ S.val` for canonical worlds

See `Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness` for:
- `int_completeness`: `IValid φ → Derivable IntPropAxiom φ`
- `int_soundness_completeness`: `IValid φ ↔ Derivable IntPropAxiom φ`

## References

* CZ Theorem 2.43
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

end Cslib.Logic.PL
