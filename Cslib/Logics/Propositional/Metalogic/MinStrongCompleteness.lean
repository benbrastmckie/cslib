/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.MinLindenbaum
public import Cslib.Logics.Propositional.Metalogic.MinSoundness

/-! # Canonical Model and Strong Completeness for Minimal Propositional Logic

This module provides the canonical Kripke model construction (prime MinTheory worlds) and proves
strong soundness and strong completeness for minimal propositional logic. Strong completeness
states that if `φ` is a minimal semantic consequence of a set `Γ`, then `φ` is set-derivable
from `Γ`.

## Main Results

### Canonical Model Infrastructure

- `MinCanonicalWorld`: Canonical world type (prime MinTheory for MinPropAxiom)
- `min_truth_lemma`: `IForces v bf S φ ↔ φ ∈ S.val` for canonical worlds

### Strong Soundness and Completeness

- `min_strong_soundness`: `SetDerivable MinPropAxiom Γ φ → MSemanticEntails Γ φ`
- `min_strong_completeness`: `MSemanticEntails Γ φ → SetDerivable MinPropAxiom Γ φ`
- `min_strong_completeness_iff`: `MSemanticEntails Γ φ ↔ SetDerivable MinPropAxiom Γ φ`
- `min_compactness`: If every finite `L ⊆ Γ` is minimally satisfiable, then `Γ` is.
- `min_completeness`: `MValid φ → Derivable MinPropAxiom φ`
- `min_soundness_completeness`: `MValid φ ↔ Derivable MinPropAxiom φ`

## Key Differences from Intuitionistic Completeness

- Worlds are MinTheory (no consistency requirement) instead of IntDCCS
- `bot_forces w = (⊥ ∈ w.val)` is a genuine predicate, not trivially `False`
- Bot case of truth lemma is `Iff.rfl` (trivial) instead of multi-step reasoning
- MValid quantifies over arbitrary upward-closed `bot_forces`, not just `fun _ => False`

## Strategy

Soundness is direct: unfold `SetDerivable` to get a witness list `L ⊆ Γ`, apply `min_soundness`
(which handles derivation trees) to get forcing of `φ` at any world where `Γ` is satisfied.

Completeness is by contraposition via the canonical model. If `φ` is not set-derivable from `Γ`,
then `φ ∉ minDeductiveClosure(Γ)`. By `min_prime_exclusion`, extend to a prime MinTheory `T`
containing `Γ` but excluding `φ`. The canonical Kripke world built from `T` satisfies all of `Γ`
but not `φ`, witnessing failure of `MSemanticEntails Γ φ`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
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

/-- The canonical `bot_forces`: `⊥` is forced at world `S` iff `⊥ ∈ S`.

Both min and int canonical worlds can be equipped with the same membership-based
`bot_forces = fun w => ⊥ ∈ w.val`. For Min, this is a genuine non-trivial predicate
(some MinTheory worlds contain `⊥`). For Int, the same predicate equals `False` at every
consistent world (see `intBotMem_iff_false` in `IntStrongCompleteness`). This unification
is the canonical-model correlate of the `BotProperties` hierarchy: both systems use the
same `bot_forces` mechanism, distinguished only by whether consistency rules out `⊥ ∈ w`. -/
def minBotForces (w : MinCanonicalWorld Atom) : Prop :=
  ⊥ ∈ w.val

/-- `bot_forces` is upward-closed: if `⊥ ∈ S` and `S ⊆ T`, then `⊥ ∈ T`. -/
theorem minBotForces_upward_closed
    {w w' : MinCanonicalWorld Atom}
    (hw : w ≤ w') (hbf : minBotForces w) : minBotForces w' :=
  hw hbf

/-- `minBotForces w ↔ ⊥ ∈ w.val` is trivially `Iff.rfl` (the definition).
Documents the shared membership-based `bot_forces` convention used by both the
minimal and intuitionistic canonical models. -/
lemma minBotForces_iff_botMem (w : MinCanonicalWorld Atom) :
    minBotForces w ↔ (⊥ : PL.Proposition Atom) ∈ w.val := Iff.rfl

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
        exact ⟨.modusPonens _ _ _
          (.modusPonens _ _ _
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
          exact ⟨.modusPonens _ _ _
            (.weakening [] _ _ (.ax [] _ (.andE1 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
      · apply (min_truth_lemma S ψ).mpr
        apply S.property.1 [φ.and ψ] ψ
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_mem
        · show (propDerivationSystem MinPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modusPonens _ _ _
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
          exact ⟨.modusPonens _ _ _
            (.weakening [] _ _ (.ax [] _ (.orI1 φ ψ)) (fun _ h => nomatch h))
            (.assumption _ _ (by simp [List.mem_cons]))⟩
      · have h_psi_S := (min_truth_lemma S ψ).mp hψ
        apply S.property.1 [ψ] (φ.or ψ)
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          exact hx ▸ h_psi_S
        · show (propDerivationSystem MinPropAxiom).Deriv _ _
          unfold propDerivationSystem Deriv
          exact ⟨.modusPonens _ _ _
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

/-! ## Strong Soundness -/

/-- **Strong Soundness for Minimal Logic**:
If `φ` is set-derivable from `Γ` using `MinPropAxiom`, then `φ` is a minimal
Kripke semantic consequence of `Γ`. -/
theorem min_strong_soundness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : SetDerivable MinPropAxiom Γ φ) : MSemanticEntails Γ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  intro World _ val bot_forces v_uc bf_uc w h_sat
  exact min_soundness d val bot_forces v_uc bf_uc w
    (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## Helper: SetDerivable and minDeductiveClosure -/

/-- `φ ∈ minDeductiveClosure(Γ)` iff `φ` is set-derivable from `Γ`. -/
theorem minDeductiveClosure_iff_SetDerivable
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    φ ∈ minDeductiveClosure Γ ↔ SetDerivable MinPropAxiom Γ φ := Iff.rfl

/-! ## Strong Completeness -/

/-- **Strong Completeness for Minimal Logic**:
If `φ` is a minimal Kripke semantic consequence of `Γ`, then `φ` is set-derivable
from `Γ` using `MinPropAxiom`.

Proof by contrapositive: assume `φ` is not set-derivable from `Γ`. Then
`φ ∉ minDeductiveClosure(Γ)`, which is a MinTheory. By `min_prime_exclusion`,
extend to a prime MinTheory `T ⊇ Γ` with `φ ∉ T`. The canonical Kripke world
from `T` satisfies all of `Γ` (since `Γ ⊆ T` and the truth lemma) but not `φ`. -/
theorem min_strong_completeness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : MSemanticEntails Γ φ) : SetDerivable MinPropAxiom Γ φ := by
  by_contra h_not
  -- φ ∉ minDeductiveClosure(Γ) (same as ¬SetDerivable by minDeductiveClosure_iff)
  have h_not_mem : φ ∉ minDeductiveClosure Γ :=
    minDeductiveClosure_iff_SetDerivable.not.mpr h_not
  -- minDeductiveClosure(Γ) is a MinTheory
  have h_theory : MinTheory (minDeductiveClosure Γ) :=
    minDeductiveClosure_is_theory Γ
  -- Extend to a prime MinTheory T ⊇ minDeductiveClosure(Γ) with φ ∉ T
  obtain ⟨T_set, hT_sup, hT_prime, hT_excl⟩ :=
    min_prime_exclusion h_theory h_not_mem
  -- Build the canonical world W₀ from T
  let W₀ : MinCanonicalWorld Atom := ⟨T_set, hT_prime⟩
  -- φ is not forced at W₀ (by min_truth_lemma and hT_excl)
  have h_not_forced : ¬ IForces minCanonicalVal minBotForces W₀ φ := by
    intro h_f
    exact hT_excl ((min_truth_lemma W₀ φ).mp h_f)
  -- All members of Γ are forced at W₀
  -- Since Γ ⊆ minDeductiveClosure(Γ) ⊆ T, all of Γ is in T
  have h_gamma_sub_T : ∀ ψ ∈ Γ, ψ ∈ T_set := by
    intro ψ hψ
    exact hT_sup (min_subset_deductive_closure Γ hψ)
  have h_gamma_forced : ∀ ψ ∈ Γ, IForces minCanonicalVal minBotForces W₀ ψ := by
    intro ψ hψ
    exact (min_truth_lemma W₀ ψ).mpr (h_gamma_sub_T ψ hψ)
  -- Instantiate MSemanticEntails to get φ forced at W₀
  have h_forced : IForces minCanonicalVal minBotForces W₀ φ :=
    h (MinCanonicalWorld Atom) minCanonicalVal minBotForces
      (fun {_ _} p hw hv => minCanonicalVal_upward_closed p hw hv)
      (fun {_ _} hw hbf => minBotForces_upward_closed hw hbf)
      W₀ h_gamma_forced
  exact h_not_forced h_forced

/-! ## Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for Minimal Logic**:
`φ` is a minimal Kripke semantic consequence of `Γ` iff `φ` is set-derivable from `Γ`. -/
@[simp]
theorem min_strong_completeness_iff {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    MSemanticEntails Γ φ ↔ SetDerivable MinPropAxiom Γ φ :=
  ⟨min_strong_completeness, min_strong_soundness⟩

/-! ## Compactness Corollary -/

/-- **Compactness for Minimal Kripke Semantics**:
If `φ` is a minimal Kripke semantic consequence of `Γ`, then there exists a finite
list `L ⊆ Γ` such that `φ` is a minimal Kripke semantic consequence of `L`.

This is the semantic compactness property: Kripke entailment is compact for
minimal logic, following directly from strong completeness + the finitary
nature of `SetDerivable`.

Proof: by strong completeness, `MSemanticEntails Γ φ → SetDerivable MinPropAxiom Γ φ`,
which gives a finite list `L ⊆ Γ`. Strong soundness then gives
`SetDerivable MinPropAxiom L φ → MSemanticEntails {ψ | ψ ∈ L} φ`. -/
theorem min_compactness {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : MSemanticEntails Γ φ) :
    ∃ L : List (PL.Proposition Atom),
      (∀ x ∈ L, x ∈ Γ) ∧
      MSemanticEntails {ψ | ψ ∈ L} φ := by
  -- By strong completeness, get a finite witness list L ⊆ Γ with L ⊢ φ
  obtain ⟨L, hL_sub, hL_deriv⟩ := min_strong_completeness h
  -- L witnesses the finite subset; by strong soundness, L-derivability gives L-entailment
  refine ⟨L, hL_sub, ?_⟩
  apply min_strong_soundness
  exact ⟨L, fun x hx => Set.mem_ofPred_eq.mpr hx, hL_deriv⟩

/-! ## Weak Completeness Corollary -/

/-- **Weak Completeness for Minimal Propositional Logic**:
If `φ` is minimally valid (forced at every world of every minimal Kripke model),
then `φ` is derivable from the empty context using `MinPropAxiom`.

This is a corollary of `min_strong_completeness`: a minimally valid formula
is a minimal semantic consequence of the empty set, so strong completeness
gives set-derivability from `∅`, and `SetDerivable_empty_iff` converts this to
ordinary derivability. -/
theorem min_completeness {φ : PL.Proposition Atom}
    (h_valid : MValid.{u, u} φ) : Derivable MinPropAxiom φ :=
  SetDerivable_empty_iff.mp
    (min_strong_completeness (MSemanticEntails_of_MValid h_valid ∅))

/-- **Soundness and Completeness for Minimal Logic**:
`φ` is minimally valid iff `φ` is derivable from the empty context
using `MinPropAxiom`.

This is a corollary of `min_strong_completeness_iff` obtained by instantiating at
`Γ = ∅` and using `SetDerivable_empty_iff`. -/
@[simp] theorem min_soundness_completeness {φ : PL.Proposition Atom} :
    MValid.{u, u} φ ↔ Derivable MinPropAxiom φ :=
  ⟨min_completeness, min_soundness_derivable⟩

end Cslib.Logic.PL
