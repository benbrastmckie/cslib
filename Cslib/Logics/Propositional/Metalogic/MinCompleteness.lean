/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Metalogic.MinSoundness
public import Cslib.Logics.Propositional.Metalogic.MinLindenbaum

/-! # Completeness Theorem for Minimal Propositional Logic

This module proves completeness for minimal propositional logic via the
canonical Kripke model construction with MinTheory (deductively closed sets)
as worlds.

## Main Results

- `MinCanonicalWorld`: Canonical world type (MinTheory for MinPropAxiom)
- `min_truth_lemma`: `IForces v bf S φ ↔ φ ∈ S.val` for canonical worlds
- `min_completeness`: `MValid φ → Derivable MinPropAxiom φ`
- `min_soundness_completeness`: `MValid φ ↔ Derivable MinPropAxiom φ`

## Key Differences from Intuitionistic Completeness

- Worlds are MinTheory (no consistency requirement) instead of IntDCCS
- `bot_forces w = (⊥ ∈ w.val)` is a genuine predicate, not trivially `False`
- Bot case of truth lemma is `Iff.rfl` (trivial) instead of multi-step reasoning
- MValid quantifies over arbitrary upward-closed `bot_forces`, not just `fun _ => False`

## References

* CZ Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Canonical Model -/

/-- A canonical world for minimal logic is a prime MinTheory for MinPropAxiom.
Worlds are prime to support the or-backward direction of the truth lemma:
if (φ ∨ ψ) ∈ S then φ ∈ S or ψ ∈ S. -/
def MinCanonicalWorld (Atom : Type*) :=
  { S : Set (PL.Proposition Atom) // MinPrimeTheory S }

/-- The canonical preorder on MinCanonicalWorld: set inclusion. -/
instance : Preorder (MinCanonicalWorld Atom) where
  le S T := S.val ⊆ T.val
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/-- The canonical valuation: atom `p` is true at world `S` iff `atom p ∈ S`. -/
def minCanonicalVal (w : MinCanonicalWorld Atom) (p : Atom) : Prop :=
  Proposition.atom p ∈ w.val

/-- The canonical valuation is upward-closed. -/
theorem minCanonicalVal_upward_closed
    {w w' : MinCanonicalWorld Atom} (p : Atom)
    (hw : w ≤ w') (hv : minCanonicalVal w p) : minCanonicalVal w' p :=
  hw hv

/-- The canonical `bot_forces`: `⊥` is forced at world `S` iff `⊥ ∈ S`. -/
def minBotForces (w : MinCanonicalWorld Atom) : Prop :=
  ⊥ ∈ w.val

/-- `bot_forces` is upward-closed: if `⊥ ∈ S` and `S ⊆ T`, then `⊥ ∈ T`. -/
theorem minBotForces_upward_closed
    {w w' : MinCanonicalWorld Atom}
    (hw : w ≤ w') (hbf : minBotForces w) : minBotForces w' :=
  hw hbf

/-! ## Truth Lemma -/

/-- **Truth Lemma**: For any canonical world `S` and formula `φ`,
`IForces minCanonicalVal minBotForces S φ ↔ φ ∈ S.val`.

Proof by structural induction on `φ` (3 cases: atom, bot, imp).
The bot case is `Iff.rfl` -- the key simplification vs intuitionistic. -/
theorem min_truth_lemma
    (S : MinCanonicalWorld Atom) :
    (φ : PL.Proposition Atom) →
    (IForces minCanonicalVal minBotForces S φ ↔ φ ∈ S.val)
  | .atom p => Iff.rfl
  | .bot => Iff.rfl
  | .and φ ψ => by
    constructor
    · -- Forward: IForces S (φ ∧ ψ) → (φ ∧ ψ) ∈ S.val
      intro ⟨hφ, hψ⟩
      have h_phi_S := (min_truth_lemma S φ).mp hφ
      have h_psi_S := (min_truth_lemma S ψ).mp hψ
      apply S.property.1 [φ, ψ] (φ.and ψ)
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        cases hx with
        | inl h => exact h ▸ h_phi_S
        | inr h => exact h ▸ h_psi_S
      · show (propDerivationSystem MinPropAxiom).Deriv _ _
        unfold propDerivationSystem Deriv
        exact ⟨.modus_ponens _ _ _
          (.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.andI φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons])))
          (.assumption _ _ (by simp [List.mem_cons]))⟩
    · -- Backward: (φ ∧ ψ) ∈ S.val → IForces S (φ ∧ ψ)
      intro h_mem
      constructor
      · apply (min_truth_lemma S φ).mpr
        apply S.property.1 [φ.and ψ] φ
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem
        · show (propDerivationSystem MinPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.andE1 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
      · apply (min_truth_lemma S ψ).mpr
        apply S.property.1 [φ.and ψ] ψ
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem
        · show (propDerivationSystem MinPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.andE2 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
  | .or φ ψ => by
    constructor
    · -- Forward: IForces S (φ ∨ ψ) → (φ ∨ ψ) ∈ S.val
      intro h_or
      rcases h_or with hφ | hψ
      · have h_phi_S := (min_truth_lemma S φ).mp hφ
        apply S.property.1 [φ] (φ.or ψ)
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_phi_S
        · show (propDerivationSystem MinPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.orI1 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
      · have h_psi_S := (min_truth_lemma S ψ).mp hψ
        apply S.property.1 [ψ] (φ.or ψ)
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_psi_S
        · show (propDerivationSystem MinPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modus_ponens _ _ _
            (.weakening [] _ _ (.ax [] _ (.orI2 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
    · -- Backward: (φ ∨ ψ) ∈ S.val → IForces S (φ ∨ ψ)
      -- Use the disjunction property of prime MinTheory worlds:
      -- (φ ∨ ψ) ∈ S → φ ∈ S ∨ ψ ∈ S.
      intro h_mem
      rcases S.property.2 φ ψ h_mem with h | h
      · exact Or.inl ((min_truth_lemma S φ).mpr h)
      · exact Or.inr ((min_truth_lemma S ψ).mpr h)
  | .imp φ ψ => by
    constructor
    · -- Forward: IForces S (φ → ψ) → (φ → ψ) ∈ S.val
      intro h_forces
      by_contra h_not_mem
      -- Get a MinTheory T' with S ⊆ T', φ ∈ T', ψ ∉ T' (using min_imp_witness)
      obtain ⟨T'_set, hST', hT'_theory, hφT', hψT'⟩ :=
        min_imp_witness S.property.1 h_not_mem
      -- Extend T' to a prime MinTheory T that still excludes ψ
      obtain ⟨T_set, hT'T, hT_prime, hψT⟩ :=
        min_prime_exclusion hT'_theory hψT'
      let T : MinCanonicalWorld Atom := ⟨T_set, hT_prime⟩
      have hle : S ≤ T := Set.Subset.trans hST' hT'T
      have hφT : φ ∈ T.val := hT'T hφT'
      have hf_φ := (min_truth_lemma T φ).mpr hφT
      have hf_ψ := h_forces T hle hf_φ
      exact hψT ((min_truth_lemma T ψ).mp hf_ψ)
    · -- Backward: (φ → ψ) ∈ S.val → IForces S (φ → ψ)
      intro h_mem T hle hf_φ
      have h_imp_T : (φ → ψ) ∈ T.val := hle h_mem
      have h_φ_T : φ ∈ T.val := (min_truth_lemma T φ).mp hf_φ
      have h_ψ_T : ψ ∈ T.val := min_theory_imp_property T.property.1 h_imp_T h_φ_T
      exact (min_truth_lemma T ψ).mpr h_ψ_T

/-! ## Completeness -/

/-- **Completeness Theorem for Minimal Propositional Logic**:

If `φ` is minimally valid (forced at every world of every minimal
Kripke model), then `φ` is derivable from the empty context using MinPropAxiom. -/
theorem min_completeness {φ : PL.Proposition Atom}
    (h_valid : MValid.{u, u} φ) : Derivable MinPropAxiom φ := by
  by_contra h_not_deriv
  have h_not_mem : φ ∉ {ψ : PL.Proposition Atom | Derivable MinPropAxiom ψ} :=
    h_not_deriv
  -- Extend the theorems theory to a prime MinTheory W₀ that excludes φ
  obtain ⟨W₀_set, _, hW₀_prime, hW₀_excl⟩ :=
    min_prime_exclusion min_theorems_theory h_not_mem
  let W₀ : MinCanonicalWorld Atom := ⟨W₀_set, hW₀_prime⟩
  have h_not_forced : ¬ IForces minCanonicalVal minBotForces W₀ φ := by
    intro h; exact hW₀_excl ((min_truth_lemma W₀ φ).mp h)
  have h_forced : IForces minCanonicalVal minBotForces W₀ φ :=
    h_valid (MinCanonicalWorld Atom) minCanonicalVal minBotForces
      (fun {_ _} p hw hv => minCanonicalVal_upward_closed p hw hv)
      (fun {_ _} hw hbf => minBotForces_upward_closed hw hbf)
      W₀
  exact h_not_forced h_forced

/-! ## Biconditional Wrapper -/

/-- **Soundness and Completeness**: `φ` is minimally valid iff `φ` is
derivable from the empty context using MinPropAxiom. -/
theorem min_soundness_completeness
    {φ : PL.Proposition Atom} :
    MValid.{u, u} φ ↔ Derivable MinPropAxiom φ :=
  ⟨min_completeness, min_soundness_derivable⟩

end Cslib.Logic.PL
