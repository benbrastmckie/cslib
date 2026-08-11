/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module


public import Cslib.Logics.Propositional.Semantics.Algebra
public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Logics.Propositional.ProofSystem.Axioms
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence

/-! # Algebraic Soundness for Propositional Logic

This module proves soundness for all three axiom tiers of propositional logic under the
generic algebraic semantics:

- `MinPropAxiom` is `GHAValid`: each minimal axiom evaluates to `⊤` in every GHA.
- `IntPropAxiom` is `HAValid`: each intuitionistic axiom evaluates to `⊤` in every HA.
- `PropositionalAxiom` is `BAValid`: each classical axiom evaluates to `⊤` in every BA.

## Main Results

- `min_alg_axiom_sound`: Each of the 8 MinPropAxiom schemata is `GHAValid`.
- `int_alg_axiom_sound`: Each of the 9 IntPropAxiom schemata is `HAValid`.
- `prop_alg_axiom_sound`: Each of the 10 PropositionalAxiom schemata is `BAValid`.
- `min_alg_soundness`: Soundness at the derivation level for minimal logic.
- `int_alg_soundness`: Soundness at the derivation level for intuitionistic logic.
- `prop_alg_soundness`: Soundness at the derivation level for classical logic.

## Key Mathlib API

- `himp_eq_top_iff`: `a ⇨ b = ⊤ ↔ a ≤ b`
- `le_himp_iff`: `a ≤ b ⇨ c ↔ a ⊓ b ≤ c`
- `himp_inf_le`: `(a ⇨ b) ⊓ a ≤ b` (modus ponens in a GHA)
- `inf_le_left`, `inf_le_right`: basic meet lemmas
- `le_sup_left`, `le_sup_right`, `inf_sup_left`: basic join lemmas
- `bot_le` (HA): `⊥ ≤ a`
- `himp_eq` (BA): `a ⇨ b = b ⊔ aᶜ`
- `compl_compl` (BA): `aᶜᶜ = a`

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Minimal Propositional Logic Soundness (GHA Level) -/

/-- Every axiom of minimal propositional logic is valid in every Generalized Heyting Algebra. -/
theorem min_alg_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : MinPropAxiom φ) : GHAValid φ := by
  intro H _ v bot_val
  cases h_ax with
  | implyK φ ψ =>
    -- implyK: φ → (ψ → φ); need φ_h ⇨ ψ_h ⇨ φ_h = ⊤
    -- By himp_eq_top_iff + le_himp_iff: φ_h ⊓ ψ_h ≤ φ_h (inf_le_left)
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff, le_himp_iff]
    exact inf_le_left
  | implyS φ ψ χ =>
    -- implyS: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
    -- After 2 rewrites: ((φ_h ⇨ ψ_h ⇨ χ_h) ⊓ (φ_h ⇨ ψ_h)) ⊓ φ_h ≤ χ_h
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff, le_himp_iff, le_himp_iff]
    -- h_pqr : ⊤ ≤ (a ⇨ b ⇨ c) (after unwrapping from ≤ chain)
    -- Actually: goal is ((a ⇨ b ⇨ c) ⊓ (a ⇨ b)) ⊓ a ≤ c
    -- Get b: ((a ⇨ b ⇨ c) ⊓ (a ⇨ b)) ⊓ a ≤ (a ⇨ b) ⊓ a ≤ b
    -- Get b ⇨ c: ((a ⇨ b ⇨ c) ⊓ (a ⇨ b)) ⊓ a ≤ (a ⇨ b ⇨ c) ⊓ a ≤ b ⇨ c
    -- Then: (b ⇨ c) ⊓ b ≤ c
    have hb : (AlgEvaluate v bot_val φ ⇨ AlgEvaluate v bot_val ψ ⇨ AlgEvaluate v bot_val χ) ⊓
              (AlgEvaluate v bot_val φ ⇨ AlgEvaluate v bot_val ψ) ⊓
              AlgEvaluate v bot_val φ ≤ AlgEvaluate v bot_val ψ :=
      (inf_le_inf_right _ inf_le_right).trans himp_inf_le
    have hbc : (AlgEvaluate v bot_val φ ⇨ AlgEvaluate v bot_val ψ ⇨ AlgEvaluate v bot_val χ) ⊓
               (AlgEvaluate v bot_val φ ⇨ AlgEvaluate v bot_val ψ) ⊓
               AlgEvaluate v bot_val φ ≤
               AlgEvaluate v bot_val ψ ⇨ AlgEvaluate v bot_val χ :=
      (inf_le_inf_right _ inf_le_left).trans himp_inf_le
    exact (le_inf hbc hb).trans himp_inf_le
  | andI φ ψ =>
    -- andI: φ → (ψ → φ ∧ ψ); after 2 rewrites: φ_h ⊓ ψ_h ≤ φ_h ⊓ ψ_h
    simp only [AlgEvaluate]
    simp [himp_eq_top_iff, le_himp_iff]
  | andE1 φ ψ =>
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff]
    exact inf_le_left
  | andE2 φ ψ =>
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff]
    exact inf_le_right
  | orI1 φ ψ =>
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff]
    exact le_sup_left
  | orI2 φ ψ =>
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff]
    exact le_sup_right
  | orE φ ψ χ =>
    -- orE: (φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))
    -- After 2 rewrites: ((φ_h ⇨ χ_h) ⊓ (ψ_h ⇨ χ_h)) ⊓ (φ_h ⊔ ψ_h) ≤ χ_h
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff, le_himp_iff, le_himp_iff]
    rw [inf_sup_left]
    apply sup_le
    · exact (inf_le_inf_right _ inf_le_left).trans himp_inf_le
    · exact (inf_le_inf_right _ inf_le_right).trans himp_inf_le

/-! ## Intuitionistic Propositional Logic Soundness (HA Level) -/

/-- Every axiom of intuitionistic propositional logic is valid in every Heyting Algebra. -/
theorem int_alg_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : IntPropAxiom φ) : HAValid φ := by
  intro H _ v
  cases h_ax with
  | implyK φ ψ => exact min_alg_axiom_sound (.implyK φ ψ) H v ⊥
  | implyS φ ψ χ => exact min_alg_axiom_sound (.implyS φ ψ χ) H v ⊥
  | andI φ ψ => exact min_alg_axiom_sound (.andI φ ψ) H v ⊥
  | andE1 φ ψ => exact min_alg_axiom_sound (.andE1 φ ψ) H v ⊥
  | andE2 φ ψ => exact min_alg_axiom_sound (.andE2 φ ψ) H v ⊥
  | orI1 φ ψ => exact min_alg_axiom_sound (.orI1 φ ψ) H v ⊥
  | orI2 φ ψ => exact min_alg_axiom_sound (.orI2 φ ψ) H v ⊥
  | orE φ ψ χ => exact min_alg_axiom_sound (.orE φ ψ χ) H v ⊥
  | efq φ =>
    -- efq: ⊥ → φ; with bot_val = ⊥: need ⊥ ⇨ φ_h = ⊤
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff]
    exact bot_le

/-! ## Classical Propositional Logic Soundness (BA Level) -/

/-- Every axiom of classical propositional logic is valid in every Boolean Algebra. -/
theorem prop_alg_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : PropositionalAxiom φ) : BAValid φ := by
  intro H _ v
  cases h_ax with
  | implyK φ ψ => exact int_alg_axiom_sound (.implyK φ ψ) H v
  | implyS φ ψ χ => exact int_alg_axiom_sound (.implyS φ ψ χ) H v
  | efq φ => exact int_alg_axiom_sound (.efq φ) H v
  | andI φ ψ => exact int_alg_axiom_sound (.andI φ ψ) H v
  | andE1 φ ψ => exact int_alg_axiom_sound (.andE1 φ ψ) H v
  | andE2 φ ψ => exact int_alg_axiom_sound (.andE2 φ ψ) H v
  | orI1 φ ψ => exact int_alg_axiom_sound (.orI1 φ ψ) H v
  | orI2 φ ψ => exact int_alg_axiom_sound (.orI2 φ ψ) H v
  | orE φ ψ χ => exact int_alg_axiom_sound (.orE φ ψ χ) H v
  | peirce φ ψ =>
    -- peirce: ((φ → ψ) → φ) → φ; need ((φ_h ⇨ ψ_h) ⇨ φ_h) ⇨ φ_h = ⊤
    -- By himp_eq_top_iff: (φ_h ⇨ ψ_h) ⇨ φ_h ≤ φ_h
    -- In BA: a ⇨ b = b ⊔ aᶜ, so (φ_h ⇨ ψ_h) ⇨ φ_h = φ_h ⊔ (φ_h ⇨ ψ_h)ᶜ ≤ φ_h
    simp only [AlgEvaluate]
    rw [himp_eq_top_iff]
    simp [himp_eq, compl_sup, compl_compl]

/-! ## Derivation-Level Soundness -/

/-- **Algebraic Soundness for Minimal Logic**: If `Γ ⊢ φ` via `MinPropAxiom`, then for
every GHA `H`, assignment `v`, and bottom value `bot_val`, if every formula in `Γ`
evaluates to `⊤` then `φ` evaluates to `⊤`. -/
theorem min_alg_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree MinPropAxiom Γ φ)
    {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → AlgEvaluate v bot_val ψ = ⊤) :
    AlgEvaluate v bot_val φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact min_alg_axiom_sound h_ax H v bot_val
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := min_alg_soundness d₁ v bot_val h_ctx
    have h2 := min_alg_soundness d₂ v bot_val h_ctx
    -- h1 : AlgEvaluate v bot_val (ψ → χ) = ⊤, i.e., ψ_h ⇨ χ_h = ⊤
    -- h2 : AlgEvaluate v bot_val ψ = ⊤, i.e., ψ_h = ⊤
    simp only [← Proposition.imp_def, AlgEvaluate] at h1
    rw [himp_eq_top_iff] at h1
    -- h1 : ψ_h ≤ χ_h; rw h2 gives ⊤ ≤ χ_h
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact min_alg_soundness d' v bot_val
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Theory-Parametric Algebraic Soundness**: If `Γ ⊢ φ` via axioms `Axioms`, then for
every GHA `H`, assignment `v`, and bottom value `bot_val`, if the valuation `v` models the
axiom theory (`v ⊨[bot_val] AxiomTheory Axioms`) and every formula in `Γ` evaluates
to `⊤`, then `φ` evaluates to `⊤`.

This generalises `min_alg_soundness` by discharging the axiom case from the `AlgTValid`
hypothesis rather than from a per-tier `*_alg_axiom_sound` lemma. -/
theorem alg_theory_soundness
    {Axioms : PL.Proposition Atom → Prop} [MinimalAxioms Axioms]
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree Axioms Γ φ)
    {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H)
    (hT : v ⊨[bot_val] AxiomTheory Axioms)
    (h_ctx : ∀ ψ, ψ ∈ Γ → AlgEvaluate v bot_val ψ = ⊤) :
    AlgEvaluate v bot_val φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact hT ψ (by simpa [AxiomTheory] using h_ax)
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := alg_theory_soundness d₁ v bot_val hT h_ctx
    have h2 := alg_theory_soundness d₂ v bot_val hT h_ctx
    simp only [← Proposition.imp_def, AlgEvaluate] at h1
    rw [himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact alg_theory_soundness d' v bot_val hT
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Algebraic Soundness for Minimal Logic (derivable)**: If `⊢ φ` via `MinPropAxiom`,
then `φ` is `GHAValid`. -/
theorem min_alg_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable MinPropAxiom φ) : GHAValid φ := by
  intro H _ v bot_val
  obtain ⟨d⟩ := h
  exact min_alg_soundness d v bot_val (fun _ h => nomatch h)

/-- **Algebraic Soundness for Intuitionistic Logic**: If `Γ ⊢ φ` via `IntPropAxiom`, then for
every HA `H` and assignment `v`, if every formula in `Γ` evaluates to `⊤` then `φ` evaluates
to `⊤`. -/
theorem int_alg_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree IntPropAxiom Γ φ)
    {H : Type*} [HeytingAlgebra H]
    (v : Atom → H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → AlgEvaluate v (⊥ : H) ψ = ⊤) :
    AlgEvaluate v (⊥ : H) φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact int_alg_axiom_sound h_ax H v
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := int_alg_soundness d₁ v h_ctx
    have h2 := int_alg_soundness d₂ v h_ctx
    simp only [← Proposition.imp_def, AlgEvaluate] at h1
    rw [himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact int_alg_soundness d' v
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Algebraic Soundness for Intuitionistic Logic (derivable)**: If `⊢ φ` via `IntPropAxiom`,
then `φ` is `HAValid`. -/
theorem int_alg_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable IntPropAxiom φ) : HAValid φ := by
  intro H _ v
  obtain ⟨d⟩ := h
  exact int_alg_soundness d v (fun _ h => nomatch h)

/-- **Algebraic Soundness for Classical Logic**: If `Γ ⊢ φ` via `PropositionalAxiom`, then for
every BA `H` and assignment `v`, if every formula in `Γ` evaluates to `⊤` then `φ` evaluates
to `⊤`. -/
theorem prop_alg_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree PropositionalAxiom Γ φ)
    {H : Type*} [BooleanAlgebra H]
    (v : Atom → H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → AlgEvaluate v (⊥ : H) ψ = ⊤) :
    AlgEvaluate v (⊥ : H) φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact prop_alg_axiom_sound h_ax H v
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := prop_alg_soundness d₁ v h_ctx
    have h2 := prop_alg_soundness d₂ v h_ctx
    simp only [← Proposition.imp_def, AlgEvaluate] at h1
    rw [himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact prop_alg_soundness d' v
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Algebraic Soundness for Classical Logic (derivable)**: If `⊢ φ` via `PropositionalAxiom`,
then `φ` is `BAValid`. -/
theorem prop_alg_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable PropositionalAxiom φ) : BAValid φ := by
  intro H _ v
  obtain ⟨d⟩ := h
  exact prop_alg_soundness d v (fun _ h => nomatch h)

end Cslib.Logic.PL
