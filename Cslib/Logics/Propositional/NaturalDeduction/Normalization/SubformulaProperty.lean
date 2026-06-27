/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Normalization.Termination

/-! # Subformula Property for Propositional Natural Deduction

This module proves that strongly normal derivations satisfy the subformula property,
and that every derivation has a strongly normal form.

## Main Results

- `Theory.Derivation.subformula_property_of_isStronglyNormal`: Strongly normal derivations
  satisfy the subformula property.
- `Theory.Derivation.subformula_property`: Every derivation has a strongly normal form
  satisfying the subformula property.

## References

* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965], Ch. III–IV.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]
variable {T : Theory Atom}

/-! ## The Subformula Property for Strongly Normal Derivations -/

/-- Strongly normal derivations satisfy the subformula property.

The proof is by structural induction. For introduction rules (andI, orI1, orI2, impI),
the formulas in sub-derivations are subformulas of the sub-derivation conclusions, which
are subformulas of the main conclusion by standard subformula relationships.

For elimination rules (andE1, andE2, orE, impE), the key is `conclusion_grounded_or_intro`:
the strongly normal condition ensures the major premise's conclusion is grounded in some
hypothesis or axiom. The IH gives all formulas in the major premise as subformulas of its
conclusion (or grounded in G/T), and since that conclusion is grounded in G/T, everything
is grounded via `IsSubformula.trans`. -/
theorem Theory.Derivation.subformula_property_of_isStronglyNormal
    {G : Ctx Atom} {A : Proposition Atom} (d : T.Derivation G A)
    (hn : d.isStronglyNormal = true) : d.SubformulaProperty := by
  intro B hB
  induction d with
  | ax h =>
    simp only [formulas, Finset.mem_singleton] at hB; subst hB
    exact Or.inr (Or.inr ⟨B, h, Proposition.IsSubformula.refl B⟩)
  | ass h =>
    simp only [formulas, Finset.mem_singleton] at hB; subst hB
    exact Or.inr (Or.inl ⟨B, h, Proposition.IsSubformula.refl B⟩)
  | andI _ D₁ D₂ ih₁ ih₂ =>
    simp only [isStronglyNormal, Bool.and_eq_true] at hn
    simp only [formulas, Finset.mem_union, Finset.mem_singleton] at hB
    obtain (rfl | hB₁) | hB₂ := hB
    · exact Or.inl (Proposition.IsSubformula.refl _)
    · rcases ih₁ hn.1 hB₁ with h | h | h
      · exact Or.inl (Proposition.IsSubformula.trans h Proposition.IsSubformula.and_left)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases ih₂ hn.2 hB₂ with h | h | h
      · exact Or.inl (Proposition.IsSubformula.trans h Proposition.IsSubformula.and_right)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  | orI1 G D ih =>
    simp only [isStronglyNormal] at hn
    simp only [formulas, Finset.mem_union, Finset.mem_singleton] at hB
    obtain rfl | hB := hB
    · exact Or.inl (Proposition.IsSubformula.refl _)
    · rcases ih hn hB with h | h | h
      · exact Or.inl (Proposition.IsSubformula.trans h Proposition.IsSubformula.or_left)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  | orI2 G D ih =>
    simp only [isStronglyNormal] at hn
    simp only [formulas, Finset.mem_union, Finset.mem_singleton] at hB
    obtain rfl | hB := hB
    · exact Or.inl (Proposition.IsSubformula.refl _)
    · rcases ih hn hB with h | h | h
      · exact Or.inl (Proposition.IsSubformula.trans h Proposition.IsSubformula.or_right)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  | impI G D ih =>
    simp only [isStronglyNormal] at hn
    simp only [formulas, Finset.mem_union, Finset.mem_singleton] at hB
    obtain rfl | hB := hB
    · exact Or.inl (Proposition.IsSubformula.refl _)
    · rcases ih hn hB with h | ⟨C, hC, hCS⟩ | h
      · exact Or.inl (Proposition.IsSubformula.trans h Proposition.IsSubformula.imp_right)
      · simp only [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact Or.inl (Proposition.IsSubformula.trans hCS Proposition.IsSubformula.imp_left)
        · exact Or.inr (Or.inl ⟨C, hC, hCS⟩)
      · exact Or.inr (Or.inr h)
  | andE1 _ D ih =>
    simp only [isStronglyNormal] at hn
    simp only [formulas, Finset.mem_union, Finset.mem_singleton] at hB
    have hn_D : D.isStronglyNormal = true := by split at hn <;> simp_all
    have hDground : conclusionGrounded D := by
      cases D with
      | andI _ _ _ => simp at hn
      | orE _ _ _ _ => simp at hn
      | ax h => exact Or.inr ⟨_, h, Proposition.IsSubformula.refl _⟩
      | ass h => exact Or.inl ⟨_, h, Proposition.IsSubformula.refl _⟩
      | andE1 _ _ | andE2 _ _ | impE _ _ =>
        rcases (conclusion_grounded_or_intro _ hn_D) with hg | hir | hore
        · exact hg
        · simp [isIntroRoot] at hir
        · simp [isOrERoot] at hore
    obtain rfl | hBD := hB
    · rcases hDground with ⟨C, hC, hCS⟩ | ⟨C, hC, hCS⟩
      · exact Or.inr (Or.inl ⟨C, hC, .trans .and_left hCS⟩)
      · exact Or.inr (Or.inr ⟨C, hC, .trans .and_left hCS⟩)
    · rcases ih hn_D hBD with hBsub | hBhyp | hBax
      · rcases hDground with ⟨C, hC, hCS⟩ | ⟨C, hC, hCS⟩
        · exact Or.inr (Or.inl ⟨C, hC, Proposition.IsSubformula.trans hBsub hCS⟩)
        · exact Or.inr (Or.inr ⟨C, hC, Proposition.IsSubformula.trans hBsub hCS⟩)
      · exact Or.inr (Or.inl hBhyp)
      · exact Or.inr (Or.inr hBax)
  | andE2 _ D ih =>
    simp only [isStronglyNormal] at hn
    simp only [formulas, Finset.mem_union, Finset.mem_singleton] at hB
    have hn_D : D.isStronglyNormal = true := by split at hn <;> simp_all
    have hDground : conclusionGrounded D := by
      cases D with
      | andI _ _ _ => simp at hn
      | orE _ _ _ _ => simp at hn
      | ax h => exact Or.inr ⟨_, h, Proposition.IsSubformula.refl _⟩
      | ass h => exact Or.inl ⟨_, h, Proposition.IsSubformula.refl _⟩
      | andE1 _ _ | andE2 _ _ | impE _ _ =>
        rcases (conclusion_grounded_or_intro _ hn_D) with hg | hir | hore
        · exact hg
        · simp [isIntroRoot] at hir
        · simp [isOrERoot] at hore
    obtain rfl | hBD := hB
    · rcases hDground with ⟨C, hC, hCS⟩ | ⟨C, hC, hCS⟩
      · exact Or.inr (Or.inl ⟨C, hC, .trans .and_right hCS⟩)
      · exact Or.inr (Or.inr ⟨C, hC, .trans .and_right hCS⟩)
    · rcases ih hn_D hBD with hBsub | hBhyp | hBax
      · rcases hDground with ⟨C, hC, hCS⟩ | ⟨C, hC, hCS⟩
        · exact Or.inr (Or.inl ⟨C, hC, Proposition.IsSubformula.trans hBsub hCS⟩)
        · exact Or.inr (Or.inr ⟨C, hC, Proposition.IsSubformula.trans hBsub hCS⟩)
      · exact Or.inr (Or.inl hBhyp)
      · exact Or.inr (Or.inr hBax)
  | orE _ D DA DB ih ihA ihB =>
    simp only [isStronglyNormal] at hn
    simp only [formulas, Finset.mem_union, Finset.mem_singleton] at hB
    have hn_parts : D.isStronglyNormal = true ∧ DA.isStronglyNormal = true ∧
        DB.isStronglyNormal = true := by
      split at hn <;> simp_all [Bool.and_eq_true]
    obtain ⟨hn_D, hn_DA, hn_DB⟩ := hn_parts
    have hDground : conclusionGrounded D := by
      cases D with
      | orI1 _ _ => simp at hn
      | orI2 _ _ => simp at hn
      | orE _ _ _ _ => simp at hn
      | ax h => exact Or.inr ⟨_, h, Proposition.IsSubformula.refl _⟩
      | ass h => exact Or.inl ⟨_, h, Proposition.IsSubformula.refl _⟩
      | andE1 _ _ | andE2 _ _ | impE _ _ =>
        rcases (conclusion_grounded_or_intro _ hn_D) with hg | hir | hore
        · exact hg
        · simp [isIntroRoot] at hir
        · simp [isOrERoot] at hore
    obtain ((rfl | hBD) | hBDA) | hBDB := hB
    · rcases (conclusion_grounded_or_intro DA hn_DA) with hgA | hirA | hireA
      · rcases hgA with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
        · simp only [Finset.mem_insert] at hC'
          rcases hC' with rfl | hC'
          · rcases hDground with ⟨D', hD', hDS⟩ | ⟨D', hD', hDS⟩
            · exact Or.inr (Or.inl ⟨D', hD', Proposition.IsSubformula.trans hCS
                (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hDS)⟩)
            · exact Or.inr (Or.inr ⟨D', hD', Proposition.IsSubformula.trans hCS
                (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hDS)⟩)
          · exact Or.inr (Or.inl ⟨C', hC', hCS⟩)
        · exact Or.inr (Or.inr ⟨C', hC', hCS⟩)
      · exact Or.inl (Proposition.IsSubformula.refl _)
      · exact Or.inl (Proposition.IsSubformula.refl _)
    · rcases ih hn_D hBD with hBsub | hBhyp | hBax
      · rcases hDground with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
        · exact Or.inr (Or.inl ⟨C', hC', Proposition.IsSubformula.trans hBsub hCS⟩)
        · exact Or.inr (Or.inr ⟨C', hC', Proposition.IsSubformula.trans hBsub hCS⟩)
      · exact Or.inr (Or.inl hBhyp)
      · exact Or.inr (Or.inr hBax)
    · rcases ihA hn_DA hBDA with hBsub | hBhyp | hBax
      · rcases (conclusion_grounded_or_intro DA hn_DA) with hgA | hirA | hireA
        · rcases hgA with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
          · simp only [Finset.mem_insert] at hC'
            rcases hC' with rfl | hC'
            · rcases hDground with ⟨D', hD', hDS⟩ | ⟨D', hD', hDS⟩
              · exact Or.inr (Or.inl ⟨D', hD', Proposition.IsSubformula.trans hBsub
                  (Proposition.IsSubformula.trans hCS
                    (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hDS))⟩)
              · exact Or.inr (Or.inr ⟨D', hD', Proposition.IsSubformula.trans hBsub
                  (Proposition.IsSubformula.trans hCS
                    (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hDS))⟩)
            · exact Or.inr (Or.inl ⟨C', hC', Proposition.IsSubformula.trans hBsub hCS⟩)
          · exact Or.inr (Or.inr ⟨C', hC', Proposition.IsSubformula.trans hBsub hCS⟩)
        · exact Or.inl (Proposition.IsSubformula.trans hBsub (Proposition.IsSubformula.refl _))
        · exact Or.inl (Proposition.IsSubformula.trans hBsub (Proposition.IsSubformula.refl _))
      · rcases hBhyp with ⟨C', hC', hCS⟩
        simp only [Finset.mem_insert] at hC'
        rcases hC' with rfl | hC'
        · rcases hDground with ⟨D', hD', hDS⟩ | ⟨D', hD', hDS⟩
          · exact Or.inr (Or.inl ⟨D', hD', Proposition.IsSubformula.trans hCS
              (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hDS)⟩)
          · exact Or.inr (Or.inr ⟨D', hD', Proposition.IsSubformula.trans hCS
              (Proposition.IsSubformula.trans Proposition.IsSubformula.or_left hDS)⟩)
        · exact Or.inr (Or.inl ⟨C', hC', hCS⟩)
      · exact Or.inr (Or.inr hBax)
    · rcases ihB hn_DB hBDB with hBsub | hBhyp | hBax
      · rcases (conclusion_grounded_or_intro DB hn_DB) with hgB | hirB | hireB
        · rcases hgB with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
          · simp only [Finset.mem_insert] at hC'
            rcases hC' with rfl | hC'
            · rcases hDground with ⟨D', hD', hDS⟩ | ⟨D', hD', hDS⟩
              · exact Or.inr (Or.inl ⟨D', hD', Proposition.IsSubformula.trans hBsub
                  (Proposition.IsSubformula.trans hCS
                    (Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hDS))⟩)
              · exact Or.inr (Or.inr ⟨D', hD', Proposition.IsSubformula.trans hBsub
                  (Proposition.IsSubformula.trans hCS
                    (Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hDS))⟩)
            · exact Or.inr (Or.inl ⟨C', hC', Proposition.IsSubformula.trans hBsub hCS⟩)
          · exact Or.inr (Or.inr ⟨C', hC', Proposition.IsSubformula.trans hBsub hCS⟩)
        · exact Or.inl (Proposition.IsSubformula.trans hBsub (Proposition.IsSubformula.refl _))
        · exact Or.inl (Proposition.IsSubformula.trans hBsub (Proposition.IsSubformula.refl _))
      · rcases hBhyp with ⟨C', hC', hCS⟩
        simp only [Finset.mem_insert] at hC'
        rcases hC' with rfl | hC'
        · rcases hDground with ⟨D', hD', hDS⟩ | ⟨D', hD', hDS⟩
          · exact Or.inr (Or.inl ⟨D', hD', Proposition.IsSubformula.trans hCS
              (Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hDS)⟩)
          · exact Or.inr (Or.inr ⟨D', hD', Proposition.IsSubformula.trans hCS
              (Proposition.IsSubformula.trans Proposition.IsSubformula.or_right hDS)⟩)
        · exact Or.inr (Or.inl ⟨C', hC', hCS⟩)
      · exact Or.inr (Or.inr hBax)
  | impE D E ih ihE =>
    simp only [isStronglyNormal] at hn
    simp only [formulas, Finset.mem_union, Finset.mem_singleton] at hB
    have hn_parts : D.isStronglyNormal = true ∧ E.isStronglyNormal = true := by
      split at hn <;> simp_all [Bool.and_eq_true]
    obtain ⟨hn_D, hn_E⟩ := hn_parts
    have hDground : conclusionGrounded D := by
      cases D with
      | impI _ _ => simp at hn
      | orE _ _ _ _ => simp at hn
      | ax h => exact Or.inr ⟨_, h, Proposition.IsSubformula.refl _⟩
      | ass h => exact Or.inl ⟨_, h, Proposition.IsSubformula.refl _⟩
      | andE1 _ _ | andE2 _ _ | impE _ _ =>
        rcases (conclusion_grounded_or_intro _ hn_D) with hg | hir | hore
        · exact hg
        · simp [isIntroRoot] at hir
        · simp [isOrERoot] at hore
    obtain ((rfl | hBD) | hBE) := hB
    · rcases hDground with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
      · exact Or.inr (Or.inl ⟨C', hC', .trans .imp_right hCS⟩)
      · exact Or.inr (Or.inr ⟨C', hC', .trans .imp_right hCS⟩)
    · rcases ih hn_D hBD with hBsub | hBhyp | hBax
      · rcases hDground with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
        · exact Or.inr (Or.inl ⟨C', hC', Proposition.IsSubformula.trans hBsub hCS⟩)
        · exact Or.inr (Or.inr ⟨C', hC', Proposition.IsSubformula.trans hBsub hCS⟩)
      · exact Or.inr (Or.inl hBhyp)
      · exact Or.inr (Or.inr hBax)
    · rcases ihE hn_E hBE with hBsub | hBhyp | hBax
      · rcases hDground with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
        · exact Or.inr (Or.inl ⟨C', hC', Proposition.IsSubformula.trans
            (Proposition.IsSubformula.trans hBsub Proposition.IsSubformula.imp_left) hCS⟩)
        · exact Or.inr (Or.inr ⟨C', hC', Proposition.IsSubformula.trans
            (Proposition.IsSubformula.trans hBsub Proposition.IsSubformula.imp_left) hCS⟩)
      · exact Or.inr (Or.inl hBhyp)
      · exact Or.inr (Or.inr hBax)

/-! ## Main Subformula Property Theorem -/

/-- The main subformula property: every derivation has a strongly normal form satisfying the
subformula property.

Proved via `exists_stronglyNormal_form` (constructive, height-free): the strongly-normal form
is built by the structural driver `snForm` from smart eliminators and substitution-normalization
([Prawitz1965], Ch. III–IV), and the subformula property of that form follows from
`subformula_property_of_isStronglyNormal`. -/
theorem Theory.Derivation.subformula_property {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) :
    ∃ (d' : T.Derivation G A), d'.isStronglyNormal = true ∧ d'.SubformulaProperty := by
  obtain ⟨d', hsn⟩ := d.exists_stronglyNormal_form
  exact ⟨d', hsn, d'.subformula_property_of_isStronglyNormal hsn⟩

end Cslib.Logic.PL
