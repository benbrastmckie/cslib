/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Normalization.Reduction
import Mathlib.Data.Multiset.DershowitzManna

/-! # Normalization Termination for Propositional Natural Deduction

This module proves termination of normalization via `redexWeight`, and establishes that
`normalize` produces strongly normal derivations.

## Main Results

- `Theory.Derivation.normalizeAux_fixpoint`: Strongly normal derivations are fixpoints of
  `normalizeAux`.
- `Theory.Derivation.normalize_isStronglyNormal`: `normalize` produces strongly normal
  derivations (proof currently `sorry` — the outstanding obligation is
  `reduceRoot_decreases_normMeasure` for the h_8 case).

## References

* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965], Ch. III–IV.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem DerivableIn

variable {Atom : Type u} [DecidableEq Atom]
variable {T : Theory Atom}

/-! ## The Key Grounding Lemma -/

/-- The conclusion of a derivation is grounded: it is a subformula of some hypothesis in `G`
or some theory axiom in `T`. Used in `conclusion_grounded_or_intro`. -/
def conclusionGrounded {G : Ctx Atom} {A : Proposition Atom}
    (_d : T.Derivation G A) : Prop :=
  (∃ C ∈ G, A.IsSubformula C) ∨ (∃ C ∈ T, A.IsSubformula C)

/-- For a strongly normal derivation, either the conclusion is grounded (a subformula of some
hypothesis or theory axiom) or the derivation is introduction-headed.

This is the key structural lemma enabling the subformula property proof. It follows
Prawitz's "top segment" analysis ([Prawitz1965], Ch. III): in a strongly normal derivation,
every elimination chain must bottom out at an axiom or assumption, and commuting conversions
are excluded, so the conclusion of any elimination is a subformula of the conclusion of
some leaf (axiom or assumption).

Proof by structural induction on `d`:
- Leaves (ax, ass): the conclusion itself is in `T`/`G`, use `IsSubformula.refl`.
- Introduction rules: the derivation is intro-headed, return right disjunct.
- Elimination rules: by strong normality, the major premise is neither introduction-headed
  nor `orE`-headed. The IH applied to the major premise yields either "grounded" or
  "intro-headed". The intro-headed case is ruled out by the pattern match in
  `isStronglyNormal`, so the major premise's conclusion is grounded. Since the derivation's
  conclusion is a subformula of the major premise's conclusion, transitivity completes the proof. -/
-- Helper: lift grounded conclusion through a subformula step.
-- If d has conclusion P and P.IsSubformula Q, and Q is grounded in G/T, then so is P.
private def liftGrounded {G : Ctx Atom} {P Q : Proposition Atom}
    (hPQ : P.IsSubformula Q)
    (hg : (∃ C ∈ G, Q.IsSubformula C) ∨ (∃ C ∈ T, Q.IsSubformula C)) :
    (∃ C ∈ G, P.IsSubformula C) ∨ (∃ C ∈ T, P.IsSubformula C) := by
  rcases hg with ⟨C, hC, hCS⟩ | ⟨C, hC, hCS⟩
  · exact Or.inl ⟨C, hC, Proposition.IsSubformula.trans hPQ hCS⟩
  · exact Or.inr ⟨C, hC, Proposition.IsSubformula.trans hPQ hCS⟩

theorem Theory.Derivation.conclusion_grounded_or_intro
    {G : Ctx Atom} {A : Proposition Atom} (d : T.Derivation G A)
    (hn : d.isStronglyNormal = true) :
    conclusionGrounded d ∨ d.isIntroRoot = true ∨ d.isOrERoot = true := by
  simp only [conclusionGrounded]
  induction d with
  | ax h =>
    exact Or.inl (Or.inr ⟨_, h, Proposition.IsSubformula.refl _⟩)
  | ass h =>
    exact Or.inl (Or.inl ⟨_, h, Proposition.IsSubformula.refl _⟩)
  | andI _ _ _ _ _ =>
    exact Or.inr (Or.inl rfl)
  | orI1 _ _ _ =>
    exact Or.inr (Or.inl rfl)
  | orI2 _ _ _ =>
    exact Or.inr (Or.inl rfl)
  | impI _ _ _ =>
    exact Or.inr (Or.inl rfl)
  | andE1 _ D ih =>
    cases D with
    | andI _ _ _ => simp [isStronglyNormal] at hn
    | orE _ _ _ _ => simp [isStronglyNormal] at hn
    | ax h => exact Or.inl (Or.inr ⟨_, h, .and_left⟩)
    | ass h => exact Or.inl (Or.inl ⟨_, h, .and_left⟩)
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal] at hn
      rcases ih hn with hg | hintro | hore
      · exact Or.inl (liftGrounded .and_left hg)
      · simp [isIntroRoot] at hintro
      · simp [isOrERoot] at hore
  | andE2 _ D ih =>
    cases D with
    | andI _ _ _ => simp [isStronglyNormal] at hn
    | orE _ _ _ _ => simp [isStronglyNormal] at hn
    | ax h => exact Or.inl (Or.inr ⟨_, h, .and_right⟩)
    | ass h => exact Or.inl (Or.inl ⟨_, h, .and_right⟩)
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal] at hn
      rcases ih hn with hg | hintro | hore
      · exact Or.inl (liftGrounded .and_right hg)
      · simp [isIntroRoot] at hintro
      · simp [isOrERoot] at hore
  | orE _ D DA DB ih ihA ihB =>
    cases D with
    | orI1 _ _ => simp [isStronglyNormal] at hn
    | orI2 _ _ => simp [isStronglyNormal] at hn
    | orE _ _ _ _ => simp [isStronglyNormal] at hn
    | ax h =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hn
      rcases ihA hn.1.2 with hgA | hirA | hireA
      · rcases hgA with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
        · simp only [Finset.mem_insert] at hC'
          rcases hC' with rfl | hC'
          · exact Or.inl (Or.inr ⟨_, h, .trans hCS .or_left⟩)
          · exact Or.inl (Or.inl ⟨C', hC', hCS⟩)
        · exact Or.inl (Or.inr ⟨C', hC', hCS⟩)
      · rcases ihB hn.2 with hgB | hirB | hireB
        · rcases hgB with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
          · simp only [Finset.mem_insert] at hC'
            rcases hC' with rfl | hC'
            · exact Or.inl (Or.inr ⟨_, h, .trans hCS .or_right⟩)
            · exact Or.inl (Or.inl ⟨C', hC', hCS⟩)
          · exact Or.inl (Or.inr ⟨C', hC', hCS⟩)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inr rfl)
    | ass h =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hn
      rcases ihA hn.1.2 with hgA | hirA | hireA
      · rcases hgA with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
        · simp only [Finset.mem_insert] at hC'
          rcases hC' with rfl | hC'
          · exact Or.inl (Or.inl ⟨_, h, .trans hCS .or_left⟩)
          · exact Or.inl (Or.inl ⟨C', hC', hCS⟩)
        · exact Or.inl (Or.inr ⟨C', hC', hCS⟩)
      · rcases ihB hn.2 with hgB | hirB | hireB
        · rcases hgB with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
          · simp only [Finset.mem_insert] at hC'
            rcases hC' with rfl | hC'
            · exact Or.inl (Or.inl ⟨_, h, .trans hCS .or_right⟩)
            · exact Or.inl (Or.inl ⟨C', hC', hCS⟩)
          · exact Or.inl (Or.inr ⟨C', hC', hCS⟩)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inr rfl)
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hn
      rcases ihA hn.1.2 with hgA | hirA | hireA
      · rcases hgA with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
        · simp only [Finset.mem_insert] at hC'
          rcases hC' with rfl | hC'
          · rcases ih hn.1.1 with hgD | hintroD | horeD
            · exact Or.inl (liftGrounded (.trans hCS .or_left) hgD)
            · simp [isIntroRoot] at hintroD
            · simp [isOrERoot] at horeD
          · exact Or.inl (Or.inl ⟨C', hC', hCS⟩)
        · exact Or.inl (Or.inr ⟨C', hC', hCS⟩)
      · rcases ihB hn.2 with hgB | hirB | hireB
        · rcases hgB with ⟨C', hC', hCS⟩ | ⟨C', hC', hCS⟩
          · simp only [Finset.mem_insert] at hC'
            rcases hC' with rfl | hC'
            · rcases ih hn.1.1 with hgD | hintroD | horeD
              · exact Or.inl (liftGrounded (.trans hCS .or_right) hgD)
              · simp [isIntroRoot] at hintroD
              · simp [isOrERoot] at horeD
            · exact Or.inl (Or.inl ⟨C', hC', hCS⟩)
          · exact Or.inl (Or.inr ⟨C', hC', hCS⟩)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inr rfl)
  | impE D E ih ihE =>
    cases D with
    | impI _ _ => simp [isStronglyNormal] at hn
    | orE _ _ _ _ => simp [isStronglyNormal] at hn
    | ax h => exact Or.inl (Or.inr ⟨_, h, .imp_right⟩)
    | ass h => exact Or.inl (Or.inl ⟨_, h, .imp_right⟩)
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hn
      rcases ih hn.1 with hgD | hintroD | horeD
      · exact Or.inl (liftGrounded .imp_right hgD)
      · simp [isIntroRoot] at hintroD
      · simp [isOrERoot] at horeD

/-! ## Normalization Termination Lemmas -/

@[simp] private theorem Theory.Derivation.normalizeAux_ax {h : A ∈ T}
    (n : Nat) : (ax h : T.Derivation G A).normalizeAux n = ax h := by
  cases n with
  | zero => rfl
  | succ n => simp [normalizeAux, reduceRoot]

@[simp] private theorem Theory.Derivation.normalizeAux_ass {h : A ∈ G}
    (n : Nat) : (ass h : T.Derivation G A).normalizeAux n = ass h := by
  cases n with
  | zero => rfl
  | succ n => simp [normalizeAux, reduceRoot]

private theorem Theory.Derivation.normalizeAux_fixpoint_aux (n : Nat) :
    ∀ {G : Ctx Atom} {A : Proposition Atom} (d : T.Derivation G A),
    d.isStronglyNormal = true → d.normalizeAux n = d := by
  induction n with
  | zero => intros; rfl
  | succ n ihn =>
    intro G A d h
    have hred : d.reduceRoot = none := by
      cases d with
      | ax _ | ass _ | andI _ _ _ | orI1 _ _ | orI2 _ _ | impI _ _ => rfl
      | andE1 _ D =>
        simp only [isStronglyNormal] at h; cases D with
        | andI _ _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
        | ax _ | ass _ | andE1 _ _ | andE2 _ _ | impE _ _ => rfl
      | andE2 _ D =>
        simp only [isStronglyNormal] at h; cases D with
        | andI _ _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
        | ax _ | ass _ | andE1 _ _ | andE2 _ _ | impE _ _ => rfl
      | orE _ D _ _ =>
        simp only [isStronglyNormal] at h; cases D with
        | orI1 _ _ | orI2 _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
        | ax _ | ass _ | andE1 _ _ | andE2 _ _ | impE _ _ => rfl
      | impE D _ =>
        simp only [isStronglyNormal] at h; cases D with
        | impI _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
        | ax _ | ass _ | andE1 _ _ | andE2 _ _ | impE _ _ => rfl
    cases d with
    | ax _ | ass _ => simp [normalizeAux, hred]
    | andI _ D₁ D₂ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at h
      simp only [normalizeAux, ihn _ h.1, ihn _ h.2, hred]
    | orI1 _ D | orI2 _ D | impI _ D =>
      simp only [isStronglyNormal] at h; simp only [normalizeAux, ihn _ h, hred]
    | andE1 _ D | andE2 _ D =>
      simp only [isStronglyNormal] at h; cases D with
      | andI _ _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
      | ax _ | ass _ | andE1 _ _ | andE2 _ _ | impE _ _ =>
        simp only [normalizeAux, ihn _ h, hred]
    | orE _ D DA DB =>
      simp only [isStronglyNormal] at h; cases D with
      | orI1 _ _ | orI2 _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
      | ax _ | ass _ =>
        simp only [isStronglyNormal, Bool.true_and, Bool.and_eq_true] at h
        simp only [normalizeAux, normalizeAux_ax, normalizeAux_ass,
          ihn _ h.1, ihn _ h.2, hred]
      | andE1 _ D' =>
        simp only [isStronglyNormal, Bool.and_eq_true] at h
        obtain ⟨⟨hD, hDA⟩, hDB⟩ := h
        simp only [normalizeAux, ihn (andE1 _ D') hD, ihn DA hDA, ihn DB hDB, hred]
      | andE2 _ D' =>
        simp only [isStronglyNormal, Bool.and_eq_true] at h
        obtain ⟨⟨hD, hDA⟩, hDB⟩ := h
        simp only [normalizeAux, ihn (andE2 _ D') hD, ihn DA hDA, ihn DB hDB, hred]
      | impE D' E' =>
        simp only [isStronglyNormal, Bool.and_eq_true] at h
        obtain ⟨⟨hD, hDA⟩, hDB⟩ := h
        simp only [normalizeAux, ihn (impE D' E') hD, ihn DA hDA, ihn DB hDB, hred]
    | impE D E =>
      simp only [isStronglyNormal] at h; cases D with
      | impI _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
      | ax _ | ass _ =>
        simp only [isStronglyNormal, Bool.true_and, Bool.and_eq_true] at h
        simp only [normalizeAux, normalizeAux_ax, normalizeAux_ass, ihn _ h, hred]
      | andE1 _ D' =>
        simp only [isStronglyNormal, Bool.and_eq_true] at h
        obtain ⟨hD, hE⟩ := h
        simp only [normalizeAux, ihn (andE1 _ D') hD, ihn E hE, hred]
      | andE2 _ D' =>
        simp only [isStronglyNormal, Bool.and_eq_true] at h
        obtain ⟨hD, hE⟩ := h
        simp only [normalizeAux, ihn (andE2 _ D') hD, ihn E hE, hred]
      | impE D' E' =>
        simp only [isStronglyNormal, Bool.and_eq_true] at h
        obtain ⟨hD, hE⟩ := h
        simp only [normalizeAux, ihn (impE D' E') hD, ihn E hE, hred]

/-- A strongly normal derivation is a fixpoint of `normalizeAux`. -/
theorem Theory.Derivation.normalizeAux_fixpoint {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) (h : d.isStronglyNormal = true) (n : Nat) :
    d.normalizeAux n = d :=
  normalizeAux_fixpoint_aux n d h

/-! ## Normalization Produces Strongly Normal Derivations -/

/-
The normalization termination proof requires a two-level induction:
1. Outer induction on formula complexity of the maximal formula being reduced
   (handles proper β-redexes via substitution)
2. Inner induction on fuel (handles commuting conversions)

Key insight (Prawitz 1965, Ch. IV): substituting `arg : G ⊢ A` into `body : G,A ⊢ B`
only creates new redexes involving `arg`. Since `arg` derives `A` (a proper subformula
of `A → B`), any new maximal formula has strictly lower complexity.
-/

private def Theory.Derivation.conclusionComplexity (_ : T.Derivation G A) : Nat := A.complexity

/-- Weight of a derivation for the termination measure. Counts redexes weighted by
formula complexity for proper β-redexes, and by 1 for commuting conversions. -/
private def Theory.Derivation.redexWeight : T.Derivation G A → Nat
  | ax _ | ass _ => 0
  | andI _ D₁ D₂ => D₁.redexWeight + D₂.redexWeight
  | andE1 _ D =>
    match D with
    | andI _ D₁ _ => D₁.conclusionComplexity + 1 + D.redexWeight
    | orE _ _ _ _ => 1 + D.redexWeight
    | _ => D.redexWeight
  | andE2 _ D =>
    match D with
    | andI _ _ D₂ => D₂.conclusionComplexity + 1 + D.redexWeight
    | orE _ _ _ _ => 1 + D.redexWeight
    | _ => D.redexWeight
  | orI1 _ D => D.redexWeight
  | orI2 _ D => D.redexWeight
  | orE _ D DA DB =>
    match D with
    | orI1 _ D0 => D0.conclusionComplexity + 1 + D.redexWeight + DA.redexWeight + DB.redexWeight
    | orI2 _ D0 => D0.conclusionComplexity + 1 + D.redexWeight + DA.redexWeight + DB.redexWeight
    | orE _ _ _ _ => 1 + D.redexWeight + DA.redexWeight + DB.redexWeight
    | _ => D.redexWeight + DA.redexWeight + DB.redexWeight
  | impI _ D => D.redexWeight
  | impE D E =>
    match D with
    | impI _ _ => E.conclusionComplexity + 1 + D.redexWeight + E.redexWeight
    | orE _ _ _ _ => 1 + D.redexWeight + E.redexWeight
    | _ => D.redexWeight + E.redexWeight

/-- Strongly normal derivations have `redexWeight = 0`: no redexes, no commuting conversions. -/
private theorem Theory.Derivation.sn_redexWeight_zero {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) (h : d.isStronglyNormal = true) : d.redexWeight = 0 := by
  induction d with
  | ax _ | ass _ => rfl
  | andI _ D₁ D₂ ih₁ ih₂ =>
    simp only [isStronglyNormal, Bool.and_eq_true] at h
    simp only [redexWeight, ih₁ h.1, ih₂ h.2]
  | andE1 _ D ih =>
    cases D with
    | andI _ _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
    | ax _ | ass _ | andE1 _ _ | andE2 _ _ | impE _ _ => exact ih h
  | andE2 _ D ih =>
    cases D with
    | andI _ _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
    | ax _ | ass _ | andE1 _ _ | andE2 _ _ | impE _ _ => exact ih h
  | orI1 _ D ih =>
    simp only [isStronglyNormal] at h; simp only [redexWeight, ih h]
  | orI2 _ D ih =>
    simp only [isStronglyNormal] at h; simp only [redexWeight, ih h]
  | orE _ D DA DB ih ihA ihB =>
    simp only [isStronglyNormal] at h
    cases D with
    | orI1 _ _ | orI2 _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
    | ax _ | ass _ =>
      simp only [isStronglyNormal, Bool.true_and, Bool.and_eq_true] at h
      simp only [redexWeight, ihA h.1, ihB h.2]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at h
      exact Nat.add_eq_zero_iff.mpr ⟨Nat.add_eq_zero_iff.mpr ⟨ih h.1.1, ihA h.1.2⟩, ihB h.2⟩
  | impI _ D ih =>
    simp only [isStronglyNormal] at h; simp only [redexWeight, ih h]
  | impE D E ih ihE =>
    cases D with
    | impI _ _ | orE _ _ _ _ => simp [isStronglyNormal] at h
    | ax _ | ass _ =>
      simp only [isStronglyNormal, Bool.true_and] at h
      simp only [redexWeight, Nat.zero_add]; exact ihE h
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at h
      exact Nat.add_eq_zero_iff.mpr ⟨ih h.1, ihE h.2⟩

/-- `redexWeight = 0` implies strongly normal: no root redex or commuting conversion
at any level means `isStronglyNormal` returns `true`. -/
private theorem Theory.Derivation.redexWeight_zero_sn {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) (h : d.redexWeight = 0) : d.isStronglyNormal = true := by
  induction d with
  | ax _ | ass _ => rfl
  | andI _ D₁ D₂ ih₁ ih₂ =>
    simp only [redexWeight] at h
    simp only [isStronglyNormal, Bool.and_eq_true]
    exact ⟨ih₁ (by omega), ih₂ (by omega)⟩
  | andE1 _ D ih =>
    cases D with
    | andI _ D₁ _ => simp only [redexWeight] at h; omega
    | orE _ _ _ _ => simp only [redexWeight] at h; omega
    | ax _ | ass _ => simp [isStronglyNormal]
    | andE1 _ _ | andE2 _ _ | impE _ _ => exact ih h
  | andE2 _ D ih =>
    cases D with
    | andI _ _ D₂ => simp only [redexWeight] at h; omega
    | orE _ _ _ _ => simp only [redexWeight] at h; omega
    | ax _ | ass _ => simp [isStronglyNormal]
    | andE1 _ _ | andE2 _ _ | impE _ _ => exact ih h
  | orI1 _ D ih =>
    simp only [redexWeight] at h; simp only [isStronglyNormal, ih h]
  | orI2 _ D ih =>
    simp only [redexWeight] at h; simp only [isStronglyNormal, ih h]
  | orE _ D DA DB ih ihA ihB =>
    cases D with
    | orI1 _ D0 => simp only [redexWeight] at h; omega
    | orI2 _ D0 => simp only [redexWeight] at h; omega
    | orE _ _ _ _ => simp only [redexWeight] at h; omega
    | ax _ | ass _ =>
      simp only [redexWeight] at h
      simp only [isStronglyNormal, Bool.and_eq_true, Bool.true_and]
      exact ⟨ihA (by omega), ihB (by omega)⟩
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [redexWeight] at h
      simp only [isStronglyNormal, Bool.and_eq_true]
      simp_all [redexWeight, isStronglyNormal, conclusionComplexity]
  | impI _ D ih =>
    simp only [redexWeight] at h; simp only [isStronglyNormal, ih h]
  | impE D E ih ihE =>
    cases D with
    | impI _ _ => simp only [redexWeight] at h; omega
    | orE _ _ _ _ => simp only [redexWeight] at h; omega
    | ax _ | ass _ =>
      simp only [redexWeight] at h
      simp only [isStronglyNormal, Bool.and_eq_true, Bool.true_and]
      exact ihE (by omega)
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [redexWeight] at h
      simp only [isStronglyNormal, Bool.and_eq_true]
      simp_all [redexWeight, isStronglyNormal, conclusionComplexity]

/-! ### Well-Founded Normalization Measure -/

/-- Total node count of a derivation tree. -/
private def Theory.Derivation.nodeCount : T.Derivation G A → Nat
  | ax _ | ass _ => 1
  | andI _ D₁ D₂ => 1 + D₁.nodeCount + D₂.nodeCount
  | andE1 _ D => 1 + D.nodeCount
  | andE2 _ D => 1 + D.nodeCount
  | orI1 _ D => 1 + D.nodeCount
  | orI2 _ D => 1 + D.nodeCount
  | orE _ D DA DB => 1 + D.nodeCount + DA.nodeCount + DB.nodeCount
  | impI _ D => 1 + D.nodeCount
  | impE D E => 1 + D.nodeCount + E.nodeCount

/-- The multiset of cut-formula complexities at beta-redex sites.
Each beta-redex contributes the complexity of the eliminated formula to this multiset.
Used as the primary component of the Dershowitz-Manna termination measure. -/
private def Theory.Derivation.maximalFormulas : T.Derivation G A → Multiset Nat
  | ax _ | ass _ => ∅
  | andI _ D₁ D₂ => D₁.maximalFormulas + D₂.maximalFormulas
  | andE1 _ D =>
    match D with
    | andI _ _ _ => {D.conclusionComplexity} + D.maximalFormulas
    | _ => D.maximalFormulas
  | andE2 _ D =>
    match D with
    | andI _ _ _ => {D.conclusionComplexity} + D.maximalFormulas
    | _ => D.maximalFormulas
  | orI1 _ D => D.maximalFormulas
  | orI2 _ D => D.maximalFormulas
  | orE _ D DA DB =>
    match D with
    | orI1 _ _ | orI2 _ _ =>
      {D.conclusionComplexity} + D.maximalFormulas + DA.maximalFormulas + DB.maximalFormulas
    | _ => D.maximalFormulas + DA.maximalFormulas + DB.maximalFormulas
  | impI _ D => D.maximalFormulas
  | impE D E =>
    match D with
    | impI _ _ => {D.conclusionComplexity} + D.maximalFormulas + E.maximalFormulas
    | _ => D.maximalFormulas + E.maximalFormulas

/-- `maximalFormulas` is invariant under weakening: it depends only on the type indices at
beta-redex sites, never on the contexts or theory. -/
private theorem Theory.Derivation.maximalFormulas_weak {T T' : Theory Atom} {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weak hTheory hCtx).maximalFormulas = D.maximalFormulas := by
  induction D generalizing T' Δ with
  | ax => rfl
  | ass => rfl
  | andI G D₁ D₂ ih₁ ih₂ =>
    simp only [Theory.Derivation.weak, maximalFormulas, ih₁, ih₂]
  | andE1 G D ih =>
    simp only [maximalFormulas] at ih ⊢
    cases D <;> simp_all [Theory.Derivation.weak, maximalFormulas, conclusionComplexity]
  | andE2 G D ih =>
    simp only [maximalFormulas] at ih ⊢
    cases D <;> simp_all [Theory.Derivation.weak, maximalFormulas, conclusionComplexity]
  | orI1 G D ih => simp only [Theory.Derivation.weak, maximalFormulas, ih]
  | orI2 G D ih => simp only [Theory.Derivation.weak, maximalFormulas, ih]
  | orE G D DA DB ih ihA ihB =>
    simp only [maximalFormulas] at ih ⊢
    cases D <;>
      simp_all [Theory.Derivation.weak, maximalFormulas, conclusionComplexity]
  | impI G D ih => simp only [Theory.Derivation.weak, maximalFormulas, ih]
  | impE D E ih ihE =>
    simp only [maximalFormulas] at ih ⊢
    cases D <;> simp_all [Theory.Derivation.weak, maximalFormulas, conclusionComplexity]

/-- Context weakening preserves `maximalFormulas` (corollary of `maximalFormulas_weak`). -/
private theorem Theory.Derivation.maximalFormulas_weakCtx {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weakCtx hCtx).maximalFormulas = D.maximalFormulas :=
  D.maximalFormulas_weak Set.Subset.rfl hCtx

/-- Casting a derivation along a context equality preserves `maximalFormulas`
(it depends only on the conclusion type indices, not on the context). -/
private theorem Theory.Derivation.maximalFormulas_cast {Γ Γ₂ : Ctx Atom}
    {A : Proposition Atom} (h : Γ = Γ₂) (D : T.Derivation Γ A) :
    (h ▸ D).maximalFormulas = D.maximalFormulas := by
  subst h; rfl

/-- `maximalFormulas` respects heterogeneous equality of derivations whose conclusion types
agree: since it depends only on type indices, casting the context cannot change it. -/
private theorem Theory.Derivation.maximalFormulas_heq {Γ Γ₂ : Ctx Atom}
    {A : Proposition Atom} {D₁ : T.Derivation Γ A} {D₂ : T.Derivation Γ₂ A}
    (hΓ : Γ = Γ₂) (hD : HEq D₁ D₂) : D₁.maximalFormulas = D₂.maximalFormulas := by
  subst hΓ; rw [eq_of_heq hD]

/-- `cast`-form: casting a derivation along an equality of derivation types preserves
`maximalFormulas`. -/
private theorem Theory.Derivation.maximalFormulas_castType {Γ Γ₂ : Ctx Atom}
    {A : Proposition Atom} (h : T.Derivation Γ A = T.Derivation Γ₂ A)
    (hΓ : Γ = Γ₂) (D : T.Derivation Γ A) :
    (cast h D).maximalFormulas = D.maximalFormulas :=
  maximalFormulas_heq hΓ.symm (cast_heq h D)

/-- `maximalFormulas` of an `andE1` elimination is bounded by the singleton of its premise's
conclusion complexity plus the premise's own `maximalFormulas` (the `{cc}` is present only at a
redex). -/
private theorem Theory.Derivation.maximalFormulas_andE1_le {G : Ctx Atom}
    {A B : Proposition Atom} (X : T.Derivation G (A ∧ B)) :
    (andE1 G X).maximalFormulas ≤ {X.conclusionComplexity} + X.maximalFormulas := by
  cases X <;> simp only [maximalFormulas] <;>
    (rw [Multiset.le_iff_count]; intro a; simp only [Multiset.count_add]; omega)

private theorem Theory.Derivation.maximalFormulas_andE2_le {G : Ctx Atom}
    {A B : Proposition Atom} (X : T.Derivation G (A ∧ B)) :
    (andE2 G X).maximalFormulas ≤ {X.conclusionComplexity} + X.maximalFormulas := by
  cases X <;> simp only [maximalFormulas] <;>
    (rw [Multiset.le_iff_count]; intro a; simp only [Multiset.count_add]; omega)

private theorem Theory.Derivation.maximalFormulas_impE_le {G : Ctx Atom}
    {A B : Proposition Atom} (X : T.Derivation G (A → B)) (Y : T.Derivation G A) :
    (impE X Y).maximalFormulas ≤
      {X.conclusionComplexity} + X.maximalFormulas + Y.maximalFormulas := by
  cases X <;> simp only [maximalFormulas] <;>
    (rw [Multiset.le_iff_count]; intro a; simp only [Multiset.count_add]; omega)

private theorem Theory.Derivation.maximalFormulas_orE_le {G : Ctx Atom}
    {A B C : Proposition Atom} (X : T.Derivation G (A ∨ B))
    (Y : T.Derivation (insert A G) C) (Z : T.Derivation (insert B G) C) :
    (orE G X Y Z).maximalFormulas ≤
      {X.conclusionComplexity} + X.maximalFormulas + Y.maximalFormulas + Z.maximalFormulas := by
  cases X <;> simp only [maximalFormulas] <;>
    (rw [Multiset.le_iff_count]; intro a; simp only [Multiset.count_add]; omega)

/-- `maximalFormulas` of a derivation cast (along a context equality) from a context-weakened
derivation equals that of the original. Used to strip the `cast (weakCtx …)` wrappers that
`subs` inserts on the branches of an `orE` (and the premise of an `impI`). -/
private theorem Theory.Derivation.maximalFormulas_cast_weakCtx {Γ Γ₂ Δ : Ctx Atom}
    {A : Proposition Atom} (h : T.Derivation Δ A = T.Derivation Γ₂ A) (hΓ : Δ = Γ₂) (hc : Γ ⊆ Δ)
    (D : T.Derivation Γ A) :
    (cast h (D.weakCtx hc)).maximalFormulas = D.maximalFormulas := by
  rw [maximalFormulas_heq (Γ := Γ₂) (Γ₂ := Δ) hΓ.symm (cast_heq h _), maximalFormulas_weakCtx]

/-- The two branch derivations of a substituted `orE` contribute exactly
`(subs Ds DA).maximalFormulas` and `(subs Ds DB).maximalFormulas`; the principal premise's
contribution is whatever `maximalFormulas` assigns to `andE`-style elimination of `subs Ds D`.
Concretely, `maximalFormulas (subs Ds (orE …))` equals the principal-premise multiset plus the
two (cast/weakened) branch multisets, with the casts stripped. -/
private theorem Theory.Derivation.maximalFormulas_subs_orE {Γ Γ' Δ : Ctx Atom}
    {A B C : Proposition Atom} (Ds : ∀ A ∈ Γ', T⇓(Δ ⊢ A)) (D : T.Derivation Γ (A ∨ B))
    (DA : T.Derivation (insert A Γ) C) (DB : T.Derivation (insert B Γ) C) :
    (subs Ds (orE Γ D DA DB)).maximalFormulas =
      (match subs Ds D with
        | orI1 _ _ | orI2 _ _ =>
          {(subs Ds D).conclusionComplexity} + (subs Ds D).maximalFormulas
        | _ => (subs Ds D).maximalFormulas) +
        (subs Ds DA).maximalFormulas + (subs Ds DB).maximalFormulas := by
  have hA : ((insert A Γ \ Γ') ∪ insert A Δ) = insert A (Γ \ Γ' ∪ Δ) := by grind
  have hB : ((insert B Γ \ Γ') ∪ insert B Δ) = insert B (Γ \ Γ' ∪ Δ) := by grind
  simp only [subs, eq_mpr_eq_cast]
  cases subs Ds D <;>
    simp only [maximalFormulas, maximalFormulas_cast_weakCtx _ hA,
      maximalFormulas_cast_weakCtx _ hB, conclusionComplexity]

/-- Membership characterization of `maximalFormulas` after substitution.
Every beta-redex complexity appearing in `subs Ds body` is one of:
- a complexity already present in `body.maximalFormulas`, or
- a complexity contributed by one of the substituted derivations `Ds A' h`, or
- the complexity of a substituted hypothesis `A' ∈ Γ'` (a *new* redex created where a
  substituted introduction meets an elimination at a former `ass A'` leaf).
Proved by induction on the structural *input* `body`, never on `subs`'s output. -/
private theorem Theory.Derivation.subs_maximalFormulas_mem {Γ Γ' Δ : Ctx Atom}
    {B : Proposition Atom} (Ds : ∀ A ∈ Γ', T⇓(Δ ⊢ A)) (body : T.Derivation Γ B)
    {k : ℕ} (hk : k ∈ (body.subs Ds).maximalFormulas) :
    k ∈ body.maximalFormulas ∨
      (∃ A', ∃ (h : A' ∈ Γ'), k ∈ (Ds A' h).maximalFormulas) ∨
      (∃ A', A' ∈ Γ' ∧ k = A'.complexity) := by
  induction body generalizing k with
  | ax hB => simp only [subs, maximalFormulas] at hk; exact absurd hk (by simp)
  | @ass Γ₀ C hC =>
    unfold subs at hk
    by_cases hmem : C ∈ Γ'
    · simp only [hmem, dif_pos] at hk
      rw [maximalFormulas_weakCtx] at hk
      exact Or.inr (Or.inl ⟨C, hmem, hk⟩)
    · simp only [hmem, dif_neg, not_false_iff] at hk
      simp only [maximalFormulas] at hk
      exact absurd hk (by simp)
  | andI G D₁ D₂ ih₁ ih₂ =>
    simp only [subs, maximalFormulas, Multiset.mem_add] at hk
    rcases hk with h | h
    · rcases ih₁ h with h' | h' | h'
      · exact Or.inl (by simp only [maximalFormulas, Multiset.mem_add]; exact Or.inl h')
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rcases ih₂ h with h' | h' | h'
      · exact Or.inl (by simp only [maximalFormulas, Multiset.mem_add]; exact Or.inr h')
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  | orI1 G D ih =>
    simp only [subs, maximalFormulas] at hk
    rcases ih hk with h' | h' | h'
    · exact Or.inl (by simp only [maximalFormulas]; exact h')
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  | orI2 G D ih =>
    simp only [subs, maximalFormulas] at hk
    rcases ih hk with h' | h' | h'
    · exact Or.inl (by simp only [maximalFormulas]; exact h')
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  | @impI A' B' G D ih =>
    unfold subs at hk
    simp only [maximalFormulas, eq_mpr_eq_cast] at hk
    rw [maximalFormulas_castType _ (by grind), maximalFormulas_weakCtx] at hk
    rcases ih hk with h' | h' | h'
    · exact Or.inl (by simp only [maximalFormulas]; exact h')
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  | @andE1 A' B' G D ih =>
    cases D with
    | ass hmem =>
      -- `D = ass (A' ∧ B')`; substitution may turn it into an introduction (a new redex).
      simp only [subs] at hk
      by_cases hΓ' : (A' ∧ B') ∈ Γ'
      · simp only [hΓ', dif_pos] at hk
        have hbound := maximalFormulas_andE1_le (G := G \ Γ' ∪ Δ)
          (weakCtx (Δ := G \ Γ' ∪ Δ) Finset.subset_union_right (Ds (A' ∧ B') hΓ'))
        rcases Multiset.mem_add.1 (Multiset.mem_of_le hbound hk) with hcc | hmf
        · rw [Multiset.mem_singleton, conclusionComplexity] at hcc
          exact Or.inr (Or.inr ⟨A' ∧ B', hΓ', hcc⟩)
        · rw [maximalFormulas_weakCtx] at hmf
          exact Or.inr (Or.inl ⟨A' ∧ B', hΓ', hmf⟩)
      · simp only [hΓ', dif_neg, not_false_iff, maximalFormulas] at hk
        exact absurd hk (by simp)
    | andI G' D₁ D₂ =>
      -- redex already present in `body`
      simp only [subs, maximalFormulas, conclusionComplexity, Multiset.mem_add,
        Multiset.mem_singleton] at hk ⊢
      rcases hk with hcc | h | h
      · exact Or.inl (Or.inl hcc)
      · rcases ih (by simp only [subs, maximalFormulas, Multiset.mem_add]; exact Or.inl h)
          with h' | h' | h'
        · exact Or.inl (Or.inr (by simpa only [maximalFormulas, Multiset.mem_add] using h'))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · rcases ih (by simp only [subs, maximalFormulas, Multiset.mem_add]; exact Or.inr h)
          with h' | h' | h'
        · exact Or.inl (Or.inr (by simpa only [maximalFormulas, Multiset.mem_add] using h'))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
    | _ =>
      -- subs preserves the head (not an introduction): no new redex here
      first
      | (rcases ih hk with h' | h' | h'
         · exact Or.inl h'
         · exact Or.inr (Or.inl h')
         · exact Or.inr (Or.inr h'))
  | @andE2 A' B' G D ih =>
    cases D with
    | ass hmem =>
      simp only [subs] at hk
      by_cases hΓ' : (A' ∧ B') ∈ Γ'
      · simp only [hΓ', dif_pos] at hk
        have hbound := maximalFormulas_andE2_le (G := G \ Γ' ∪ Δ)
          (weakCtx (Δ := G \ Γ' ∪ Δ) Finset.subset_union_right (Ds (A' ∧ B') hΓ'))
        rcases Multiset.mem_add.1 (Multiset.mem_of_le hbound hk) with hcc | hmf
        · rw [Multiset.mem_singleton, conclusionComplexity] at hcc
          exact Or.inr (Or.inr ⟨A' ∧ B', hΓ', hcc⟩)
        · rw [maximalFormulas_weakCtx] at hmf
          exact Or.inr (Or.inl ⟨A' ∧ B', hΓ', hmf⟩)
      · simp only [hΓ', dif_neg, not_false_iff, maximalFormulas] at hk
        exact absurd hk (by simp)
    | andI G' D₁ D₂ =>
      simp only [subs, maximalFormulas, conclusionComplexity, Multiset.mem_add,
        Multiset.mem_singleton] at hk ⊢
      rcases hk with hcc | h | h
      · exact Or.inl (Or.inl hcc)
      · rcases ih (by simp only [subs, maximalFormulas, Multiset.mem_add]; exact Or.inl h)
          with h' | h' | h'
        · exact Or.inl (Or.inr (by simpa only [maximalFormulas, Multiset.mem_add] using h'))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · rcases ih (by simp only [subs, maximalFormulas, Multiset.mem_add]; exact Or.inr h)
          with h' | h' | h'
        · exact Or.inl (Or.inr (by simpa only [maximalFormulas, Multiset.mem_add] using h'))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
    | _ =>
      rcases ih hk with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  | @orE A' B' C' G D DA DB ih ihA ihB =>
    -- route members of the branch derivations, mapping the first disjunct into
    -- `(orE G D DA DB).maximalFormulas` (the `DA`/`DB` summands).
    have routeA : ∀ {m : ℕ}, m ∈ (subs Ds DA).maximalFormulas →
        m ∈ (orE G D DA DB).maximalFormulas ∨
          (∃ A'', ∃ (h : A'' ∈ Γ'), m ∈ maximalFormulas (Ds A'' h)) ∨
          (∃ A'', A'' ∈ Γ' ∧ m = A''.complexity) := by
      intro m hm
      rcases ihA hm with h' | h' | h'
      · refine Or.inl ?_
        cases D <;> simp only [maximalFormulas, Multiset.mem_add] <;>
          first
          | exact Or.inl (Or.inr h')
          | exact Or.inl (Or.inl (Or.inr h'))
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    have routeB : ∀ {m : ℕ}, m ∈ (subs Ds DB).maximalFormulas →
        m ∈ (orE G D DA DB).maximalFormulas ∨
          (∃ A'', ∃ (h : A'' ∈ Γ'), m ∈ maximalFormulas (Ds A'' h)) ∨
          (∃ A'', A'' ∈ Γ' ∧ m = A''.complexity) := by
      intro m hm
      rcases ihB hm with h' | h' | h'
      · refine Or.inl ?_
        cases D <;> simp only [maximalFormulas, Multiset.mem_add] <;> exact Or.inr h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    -- The two branches always reduce (after stripping casts/weakenings) to `(subs Ds DA/DB).mf`.
    rw [maximalFormulas_subs_orE] at hk
    cases D with
    | ass hmem =>
      simp only [subs] at hk
      by_cases hΓ' : (A' ∨ B') ∈ Γ'
      · simp only [hΓ', dif_pos] at hk
        rw [Multiset.add_assoc] at hk
        rcases Multiset.mem_add.1 hk with hPP | hBr
        · -- principal premise side; case on whether the substituted derivation is an `orI` redex.
          have hmem' : k ∈ {(Ds (A' ∨ B') hΓ').conclusionComplexity} +
              (Ds (A' ∨ B') hΓ').maximalFormulas := by
            revert hPP
            split <;> intro hPP <;>
              simp only [maximalFormulas_weakCtx, conclusionComplexity, Multiset.mem_add,
                Multiset.mem_singleton] at hPP ⊢ <;>
              tauto
          rcases Multiset.mem_add.1 hmem' with hcc | hmf
          · rw [Multiset.mem_singleton, conclusionComplexity] at hcc
            exact Or.inr (Or.inr ⟨A' ∨ B', hΓ', hcc⟩)
          · exact Or.inr (Or.inl ⟨A' ∨ B', hΓ', hmf⟩)
        · rcases Multiset.mem_add.1 hBr with hA | hB
          · exact routeA hA
          · exact routeB hB
      · simp only [hΓ', dif_neg, not_false_iff, maximalFormulas, Multiset.mem_add] at hk
        rcases hk with (hk | hA) | hB
        · exact absurd hk (by simp)
        · exact routeA hA
        · exact routeB hB
    | orI1 G' D₀ =>
      simp only [subs, maximalFormulas, conclusionComplexity, Multiset.mem_add,
        Multiset.mem_singleton] at hk ⊢
      rcases hk with ((hcc | hD) | hA) | hB
      · exact Or.inl (Or.inl (Or.inl (Or.inl hcc)))
      · rcases ih (by simp only [subs, maximalFormulas]; exact hD) with h' | h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inr (by simpa only [maximalFormulas] using h'))))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · simpa only [maximalFormulas, conclusionComplexity, Multiset.mem_add,
          Multiset.mem_singleton] using routeA hA
      · simpa only [maximalFormulas, conclusionComplexity, Multiset.mem_add,
          Multiset.mem_singleton] using routeB hB
    | orI2 G' D₀ =>
      simp only [subs, maximalFormulas, conclusionComplexity, Multiset.mem_add,
        Multiset.mem_singleton] at hk ⊢
      rcases hk with ((hcc | hD) | hA) | hB
      · exact Or.inl (Or.inl (Or.inl (Or.inl hcc)))
      · rcases ih (by simp only [subs, maximalFormulas]; exact hD) with h' | h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inr (by simpa only [maximalFormulas] using h'))))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · simpa only [maximalFormulas, conclusionComplexity, Multiset.mem_add,
          Multiset.mem_singleton] using routeA hA
      · simpa only [maximalFormulas, conclusionComplexity, Multiset.mem_add,
          Multiset.mem_singleton] using routeB hB
    | _ =>
      simp only [subs, maximalFormulas, Multiset.mem_add] at hk
      rcases hk with (hD | hA) | hB
      · rcases ih (by simp only [subs, maximalFormulas]; exact hD) with h' | h' | h'
        · exact Or.inl (by
            simp only [maximalFormulas, Multiset.mem_add]; exact Or.inl (Or.inl h'))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · exact routeA hA
      · exact routeB hB
  | @impE G A' B' D E ih ihE =>
    -- helper: route a member of `(subs Ds E).maximalFormulas` (the argument side).
    have routeE : ∀ {m : ℕ}, m ∈ (subs Ds E).maximalFormulas →
        m ∈ E.maximalFormulas ∨
          (∃ A'', ∃ (h : A'' ∈ Γ'), m ∈ maximalFormulas (Ds A'' h)) ∨
          (∃ A'', A'' ∈ Γ' ∧ m = A''.complexity) := fun hm => ihE hm
    cases D with
    | ass hmem =>
      simp only [subs, maximalFormulas] at hk
      by_cases hΓ' : (A' → B') ∈ Γ'
      · simp only [hΓ', dif_pos] at hk
        have hbound := maximalFormulas_impE_le (G := G \ Γ' ∪ Δ)
          (weakCtx (Δ := G \ Γ' ∪ Δ) Finset.subset_union_right (Ds (A' → B') hΓ'))
          (subs Ds E)
        rcases Multiset.mem_add.1 (Multiset.mem_of_le hbound hk) with hL | hE
        · rcases Multiset.mem_add.1 hL with hcc | hmf
          · rw [Multiset.mem_singleton, conclusionComplexity] at hcc
            exact Or.inr (Or.inr ⟨A' → B', hΓ', hcc⟩)
          · rw [maximalFormulas_weakCtx] at hmf
            exact Or.inr (Or.inl ⟨A' → B', hΓ', hmf⟩)
        · rcases routeE hE with h' | h' | h'
          · exact Or.inl (by simp only [maximalFormulas]; exact Multiset.mem_add.2 (Or.inr h'))
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
      · simp only [hΓ', dif_neg, not_false_iff, maximalFormulas, Multiset.mem_add] at hk
        rcases hk with hk | hE
        · exact absurd hk (by simp)
        · rcases routeE hE with h' | h' | h'
          · exact Or.inl (by simp only [maximalFormulas]; exact Multiset.mem_add.2 (Or.inr h'))
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
    | impI G' D₀ =>
      simp only [subs, maximalFormulas, conclusionComplexity, Multiset.mem_add,
        Multiset.mem_singleton] at hk ⊢
      rcases hk with (hcc | hD) | hE
      · exact Or.inl (Or.inl (Or.inl hcc))
      · rcases ih (by simp only [subs, maximalFormulas]; exact hD) with h' | h' | h'
        · exact Or.inl (Or.inl (Or.inr (by
            simpa only [maximalFormulas, conclusionComplexity] using h')))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · rcases routeE hE with h' | h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
    | _ =>
      simp only [subs, maximalFormulas, Multiset.mem_add] at hk
      rcases hk with hD | hE
      · rcases ih (by simp only [subs, maximalFormulas]; exact hD) with h' | h' | h'
        · exact Or.inl (by simp only [maximalFormulas, Multiset.mem_add]; exact Or.inl h')
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
      · rcases routeE hE with h' | h' | h'
        · exact Or.inl (by simp only [maximalFormulas, Multiset.mem_add]; exact Or.inr h')
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')

/-- Specialization of `subs_maximalFormulas_mem` to single-hypothesis substitution `subsOne`.
Every beta-redex complexity in `D.subsOne E` that is *new* (not already present in `D`) is either
contributed by the substituted derivation `E` (which derives the hypothesis `A`), or is exactly
`A.complexity` — the complexity of the substituted hypothesis. In the β-reduction cases that drive
normalization, `A` is a *proper subformula* of the eliminated cut formula, so each new redex is
strictly smaller; under the strong-normality invariant of Phase 2b, `E.maximalFormulas = ∅`, so the
only new redexes have complexity `A.complexity`. ([Prawitz1965], Ch. III–IV.) -/
private theorem Theory.Derivation.subsOne_new_redex_complexity_lt {A B : Proposition Atom}
    {Γ : Ctx Atom} (D : T.Derivation (insert A Γ) B) (E : T.Derivation Γ A) {k : ℕ}
    (hk : k ∈ (D.subsOne E).maximalFormulas) (hnew : k ∉ D.maximalFormulas) :
    k ∈ E.maximalFormulas ∨ k = A.complexity := by
  -- `subsOne` is `subs` with `Γ' = {A}`, `Δ = Γ`, and the substituted family sending `A ↦ E`.
  unfold subsOne at hk
  rw [maximalFormulas_cast (h := by ext x; simp; tauto)] at hk
  rcases subs_maximalFormulas_mem _ D hk with h | ⟨A', hA', hmem⟩ | ⟨A', hA', heq⟩
  · exact absurd h hnew
  · -- `A' ∈ {A}` forces `A' = A`, and the substituted derivation is `E` (up to a cast).
    rw [Finset.mem_singleton] at hA'
    subst hA'
    left
    simpa using hmem
  · rw [Finset.mem_singleton] at hA'
    subst hA'
    exact Or.inr heq

/-- Sum of the `nodeCount` of each sub-derivation rooted at a commuting conversion site.
A commuting conversion occurs when an elimination is applied to the result of `orE`.
Used as the secondary component of the termination measure. -/
private def Theory.Derivation.commutingSum : T.Derivation G A → Nat
  | ax _ | ass _ => 0
  | andI _ D₁ D₂ => D₁.commutingSum + D₂.commutingSum
  | andE1 _ D =>
    match D with
    | orE _ _ _ _ => D.nodeCount + D.commutingSum
    | _ => D.commutingSum
  | andE2 _ D =>
    match D with
    | orE _ _ _ _ => D.nodeCount + D.commutingSum
    | _ => D.commutingSum
  | orI1 _ D => D.commutingSum
  | orI2 _ D => D.commutingSum
  | orE _ D DA DB =>
    match D with
    | orE _ _ _ _ => D.nodeCount + D.commutingSum + DA.commutingSum + DB.commutingSum
    | _ => D.commutingSum + DA.commutingSum + DB.commutingSum
  | impI _ D => D.commutingSum
  | impE D E =>
    match D with
    | orE _ _ _ _ => D.nodeCount + D.commutingSum + E.commutingSum
    | _ => D.commutingSum + E.commutingSum

/-- `nodeCount` is invariant under weakening: `weak` preserves the tree structure. -/
private theorem Theory.Derivation.nodeCount_weak {T T' : Theory Atom} {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weak hTheory hCtx).nodeCount = D.nodeCount := by
  induction D generalizing T' Δ with
  | ax => rfl
  | ass => rfl
  | andI G D₁ D₂ ih₁ ih₂ => simp only [Theory.Derivation.weak, nodeCount, ih₁, ih₂]
  | andE1 G D ih => simp only [Theory.Derivation.weak, nodeCount, ih]
  | andE2 G D ih => simp only [Theory.Derivation.weak, nodeCount, ih]
  | orI1 G D ih => simp only [Theory.Derivation.weak, nodeCount, ih]
  | orI2 G D ih => simp only [Theory.Derivation.weak, nodeCount, ih]
  | orE G D DA DB ih ihA ihB => simp only [Theory.Derivation.weak, nodeCount, ih, ihA, ihB]
  | impI G D ih => simp only [Theory.Derivation.weak, nodeCount, ih]
  | impE D E ih ihE => simp only [Theory.Derivation.weak, nodeCount, ih, ihE]

/-- `nodeCount` is invariant under context weakening. -/
private theorem Theory.Derivation.nodeCount_weakCtx {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weakCtx hCtx).nodeCount = D.nodeCount :=
  D.nodeCount_weak Set.Subset.rfl hCtx

/-- `commutingSum` is invariant under weakening: `weak` preserves the tree structure, on
which `commutingSum` (and the `nodeCount` it references) depends. -/
private theorem Theory.Derivation.commutingSum_weak {T T' : Theory Atom} {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weak hTheory hCtx).commutingSum = D.commutingSum := by
  induction D generalizing T' Δ with
  | ax => rfl
  | ass => rfl
  | andI G D₁ D₂ ih₁ ih₂ => simp only [Theory.Derivation.weak, commutingSum, ih₁, ih₂]
  | andE1 G D ih =>
    simp only [commutingSum] at ih ⊢
    cases D <;> simp_all [Theory.Derivation.weak, commutingSum, nodeCount_weak, nodeCount]
  | andE2 G D ih =>
    simp only [commutingSum] at ih ⊢
    cases D <;> simp_all [Theory.Derivation.weak, commutingSum, nodeCount_weak, nodeCount]
  | orI1 G D ih => simp only [Theory.Derivation.weak, commutingSum, ih]
  | orI2 G D ih => simp only [Theory.Derivation.weak, commutingSum, ih]
  | orE G D DA DB ih ihA ihB =>
    simp only [Theory.Derivation.weak, commutingSum, ih, ihA, ihB, nodeCount_weak]
    cases D <;> simp [Theory.Derivation.weak, nodeCount_weak]
  | impI G D ih => simp only [Theory.Derivation.weak, commutingSum, ih]
  | impE D E ih ihE =>
    simp only [Theory.Derivation.weak, commutingSum, ih, ihE, nodeCount_weak]
    cases D <;> simp [Theory.Derivation.weak, nodeCount_weak]

/-- `commutingSum` is invariant under context weakening. -/
private theorem Theory.Derivation.commutingSum_weakCtx {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weakCtx hCtx).commutingSum = D.commutingSum :=
  D.commutingSum_weak Set.Subset.rfl hCtx

/-- A strongly normal derivation contains no beta-redexes, hence its `maximalFormulas`
multiset is empty: the `{cc}` summand is contributed exactly at the proper-redex positions
(`andE1`/`andE2` of `andI`, `orE` of `orI1`/`orI2`, `impE` of `impI`) that `isStronglyNormal`
forbids. -/
private theorem Theory.Derivation.maximalFormulas_sn_eq_zero
    {G : Ctx Atom} {A : Proposition Atom} (d : T.Derivation G A)
    (hd : d.isStronglyNormal = true) : d.maximalFormulas = ∅ := by
  induction d with
  | ax _ | ass _ => rfl
  | andI _ D₁ D₂ ih₁ ih₂ =>
    simp only [isStronglyNormal, Bool.and_eq_true] at hd
    simp [maximalFormulas, ih₁ hd.1, ih₂ hd.2]
  | andE1 _ D ih =>
    cases D with
    | andI _ _ _ => simp [isStronglyNormal] at hd
    | orE _ _ _ _ => simp [isStronglyNormal] at hd
    | ax _ | ass _ => simp only [maximalFormulas]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal] at hd
      simpa only [maximalFormulas] using ih hd
  | andE2 _ D ih =>
    cases D with
    | andI _ _ _ => simp [isStronglyNormal] at hd
    | orE _ _ _ _ => simp [isStronglyNormal] at hd
    | ax _ | ass _ => simp only [maximalFormulas]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal] at hd
      simpa only [maximalFormulas] using ih hd
  | orI1 _ D ih => simp only [isStronglyNormal] at hd; simpa only [maximalFormulas] using ih hd
  | orI2 _ D ih => simp only [isStronglyNormal] at hd; simpa only [maximalFormulas] using ih hd
  | orE _ D DA DB ih ihA ihB =>
    cases D with
    | orI1 _ _ => simp [isStronglyNormal] at hd
    | orI2 _ _ => simp [isStronglyNormal] at hd
    | orE _ _ _ _ => simp [isStronglyNormal] at hd
    | ax _ | ass _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hd
      simp [maximalFormulas, ihA hd.1.2, ihB hd.2]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hd
      have h1 := ih hd.1.1; have h2 := ihA hd.1.2; have h3 := ihB hd.2
      simp only [maximalFormulas] at h1 ⊢; rw [h2, h3]; simpa using h1
  | impI _ D ih => simp only [isStronglyNormal] at hd; simpa only [maximalFormulas] using ih hd
  | impE D E ih ihE =>
    cases D with
    | impI _ _ => simp [isStronglyNormal] at hd
    | orE _ _ _ _ => simp [isStronglyNormal] at hd
    | ax _ | ass _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hd
      simp [maximalFormulas, ihE hd.2]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hd
      have h1 := ih hd.1; have h2 := ihE hd.2
      simp only [maximalFormulas] at h1 ⊢; rw [h2]; simpa using h1

/-- A strongly normal derivation contains no commuting conversions, hence its `commutingSum`
is zero: the `nodeCount + ...` summand is contributed exactly at the commuting-conversion
positions (`andE1`/`andE2` of `orE`, `impE` of `orE`) that `isStronglyNormal` forbids. -/
private theorem Theory.Derivation.commutingSum_sn_eq_zero
    {G : Ctx Atom} {A : Proposition Atom} (d : T.Derivation G A)
    (hd : d.isStronglyNormal = true) : d.commutingSum = 0 := by
  induction d with
  | ax _ | ass _ => rfl
  | andI _ D₁ D₂ ih₁ ih₂ =>
    simp only [isStronglyNormal, Bool.and_eq_true] at hd
    simp [commutingSum, ih₁ hd.1, ih₂ hd.2]
  | andE1 _ D ih =>
    cases D with
    | andI _ _ _ => simp [isStronglyNormal] at hd
    | orE _ _ _ _ => simp [isStronglyNormal] at hd
    | ax _ | ass _ => simp only [commutingSum]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal] at hd
      simpa only [commutingSum] using ih hd
  | andE2 _ D ih =>
    cases D with
    | andI _ _ _ => simp [isStronglyNormal] at hd
    | orE _ _ _ _ => simp [isStronglyNormal] at hd
    | ax _ | ass _ => simp only [commutingSum]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal] at hd
      simpa only [commutingSum] using ih hd
  | orI1 _ D ih => simp only [isStronglyNormal] at hd; simpa only [commutingSum] using ih hd
  | orI2 _ D ih => simp only [isStronglyNormal] at hd; simpa only [commutingSum] using ih hd
  | orE _ D DA DB ih ihA ihB =>
    cases D with
    | orI1 _ _ => simp [isStronglyNormal] at hd
    | orI2 _ _ => simp [isStronglyNormal] at hd
    | orE _ _ _ _ => simp [isStronglyNormal] at hd
    | ax _ | ass _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hd
      simp [commutingSum, ihA hd.1.2, ihB hd.2]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hd
      have h1 := ih hd.1.1; have h2 := ihA hd.1.2; have h3 := ihB hd.2
      simp only [commutingSum] at h1 ⊢; omega
  | impI _ D ih => simp only [isStronglyNormal] at hd; simpa only [commutingSum] using ih hd
  | impE D E ih ihE =>
    cases D with
    | impI _ _ => simp [isStronglyNormal] at hd
    | orE _ _ _ _ => simp [isStronglyNormal] at hd
    | ax _ | ass _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hd
      simp [commutingSum, ihE hd.2]
    | andE1 _ _ | andE2 _ _ | impE _ _ =>
      simp only [isStronglyNormal, Bool.and_eq_true] at hd
      have h1 := ih hd.1; have h2 := ihE hd.2
      simp only [commutingSum] at h1 ⊢; omega

/-- The strong-normality invariant on the *immediate* sub-derivations consumed by
`reduceRoot`. This is the genuine side condition under which a single root reduction strictly
decreases `normMeasure`:

* For the proper β-redexes (`impE (impI D) E`, `andEᵢ (andI ..)`, `orE (orIᵢ D) DA ..`):
  **all** derivations involved in the substitution must be strongly normal.
  - `impE (impI D) E → D.subsOne E`: both the body `D` and the argument `E` must be strongly
    normal.  Since `D.maximalFormulas = ∅`, every element of `(D.subsOne E).maximalFormulas` is
    either in `E.maximalFormulas = ∅` or has complexity `A.complexity` (where `A` is the
    hypothesis type), which is strictly less than `(A → B).complexity`.
  - `orE (orI₁ D) DA _`: both `D` (the injected proof) and `DA` (the body) must be strongly
    normal, for the same reason: `DA.maximalFormulas = ∅` and `D.maximalFormulas = ∅`, so every
    new redex created by `DA.subsOne D` has complexity `A.complexity < (A ∨ B).complexity`.
  - Similarly for `orE (orI₂ D) _ DB`.
  - For `andEᵢ (andI ..)` the result is the sibling sub-derivation; no substitution occurs, so
    only the *other* sub-derivation (which is discarded) must be strongly normal — it contributes
    `D₂.maximalFormulas` to the source multiset, which is removed by the reduction.
* For the commuting conversions (`andEᵢ (orE ..)`, `impE (orE ..) ..`) the two branch
  derivations of the inner `orE` must be strongly normal, which guarantees that pushing the
  elimination inside the branches creates no new maximal formula (the branch is not an
  introduction at the eliminated connective), so `maximalFormulas` is preserved and the strictly
  smaller `commutingSum` drives the decrease.

For all derivations that are *not* `reduceRoot`-redexes the invariant is vacuously `True`, since
`reduceRoot` returns `none` there and the theorem's hypothesis `d.reduceRoot = some d'` is
unsatisfiable. -/
private def Theory.Derivation.reduceRootSubSN : T.Derivation G A → Prop
  | impE (impI _ D) E => D.isStronglyNormal = true ∧ E.isStronglyNormal = true
  | andE1 _ (andI _ _ D₂) => D₂.isStronglyNormal = true
  | andE2 _ (andI _ D₁ _) => D₁.isStronglyNormal = true
  | orE _ (orI1 _ D) DA _ => D.isStronglyNormal = true ∧ DA.isStronglyNormal = true
  | orE _ (orI2 _ D) _ DB => D.isStronglyNormal = true ∧ DB.isStronglyNormal = true
  | andE1 _ (orE _ _ DA DB) =>
    (andE1 _ DA).isStronglyNormal = true ∧ (andE1 _ DB).isStronglyNormal = true
  | andE2 _ (orE _ _ DA DB) =>
    (andE2 _ DA).isStronglyNormal = true ∧ (andE2 _ DB).isStronglyNormal = true
  | impE (orE _ _ DA DB) E =>
    (impE DA (E.weakCtx (Finset.subset_insert _ _))).isStronglyNormal = true ∧
      (impE DB (E.weakCtx (Finset.subset_insert _ _))).isStronglyNormal = true
  | _ => True

/-- Strictly enlarging a multiset by a nonempty multiset gives a Dershowitz–Manna-larger
multiset: with `Y = ∅` the side condition on `Y` is vacuous, so `X < X + Z` whenever `Z ≠ ∅`. -/
private theorem Multiset.isDershowitzMannaLT_add_right {X Z : Multiset ℕ} (hZ : Z ≠ ∅) :
    Multiset.IsDershowitzMannaLT X (X + Z) :=
  ⟨X, ∅, Z, hZ, by simp, rfl, by simp⟩

/-- Adding a fresh element `c` on top of `M + N` is Dershowitz–Manna-larger than `M`: the
removed multiset `Z = c ::ₘ N` is nonempty and the added multiset `Y` is empty. This is the
exact shape of the primary-component decrease in the conjunction β-reduction cases. -/
private theorem Multiset.isDershowitzMannaLT_cons_add {c : ℕ} {M N : Multiset ℕ} :
    Multiset.IsDershowitzMannaLT M (c ::ₘ (M + N)) :=
  ⟨M, ∅, c ::ₘ N, by simp, by simp, by rw [Multiset.add_cons], by simp⟩

/-- The right-hand companion of `isDershowitzMannaLT_cons_add`: `N < c ::ₘ (M + N)`. -/
private theorem Multiset.isDershowitzMannaLT_cons_add' {c : ℕ} {M N : Multiset ℕ} :
    Multiset.IsDershowitzMannaLT N (c ::ₘ (M + N)) := by
  rw [add_comm]; exact Multiset.isDershowitzMannaLT_cons_add

/-- A single-cut Dershowitz–Manna step: removing one element `a` from `N = X + {a}` and replacing
it by a multiset `Y` all of whose elements are `< a` yields a strictly smaller multiset
`M = X + Y`. -/
private theorem Multiset.isDershowitzMannaLT_remove_add_lt {a : ℕ} {X Y : Multiset ℕ}
    (hY : ∀ y ∈ Y, y < a) :
    Multiset.IsDershowitzMannaLT (X + Y) (X + {a}) :=
  ⟨X, Y, {a}, by simp, rfl, rfl, fun y hy => ⟨a, by simp, hY y hy⟩⟩

/-- The combined termination measure for normalization:
the pair `(maximalFormulas d, commutingSum d)` ordered by the lexicographic product of
the Dershowitz-Manna multiset ordering and the natural number ordering. -/
private def Theory.Derivation.normMeasure (d : T.Derivation G A) : Multiset Nat × Nat :=
  (d.maximalFormulas, d.commutingSum)

/-- The combined normalization measure is well-founded. -/
private theorem normMeasure_wf :
    WellFounded (InvImage (Prod.Lex Multiset.IsDershowitzMannaLT (· < ·))
      (@Theory.Derivation.normMeasure Atom _ T G A)) :=
  InvImage.wf _ (WellFounded.prod_lex
    Multiset.wellFounded_isDershowitzMannaLT
    Nat.lt_wfRel.wf)

/-! A single root reduction strictly decreases the `normMeasure` in the lexicographic
Dershowitz–Manna × `<` order, provided the immediate sub-derivations consumed by the reduction
satisfy the strong-normality invariant `reduceRootSubSN`.

* β-redexes (`impE (impI ..) E`, `andEᵢ (andI ..)`, `orE (orIᵢ ..) ..`) decrease the primary
  `maximalFormulas` component: the eliminated cut formula is removed and any redex newly created
  by the substitution is strictly smaller (`subsOne_new_redex_complexity_lt`), so `Prod.Lex.left`
  applies.
* Commuting conversions (`andEᵢ (orE ..)`, `impE (orE ..) ..`) keep `maximalFormulas` fixed
  (the branches are not introductions at the eliminated connective, by the invariant) and strictly
  decrease the secondary `commutingSum` component (the `orE` site is no longer directly below an
  elimination), so `Prod.Lex.right` applies. ([Prawitz1965], Ch. III–IV.)

`reduceRoot_decreases_normMeasure` is proved below. -/

set_option maxHeartbeats 1200000 in
/-- A single root reduction strictly decreases the combined normalization measure. -/
private theorem Theory.Derivation.reduceRoot_decreases_normMeasure
    {G : Ctx Atom} {A : Proposition Atom} (d : T.Derivation G A)
    (h_subsSN : d.reduceRootSubSN)
    (d' : T.Derivation G A) (hd' : d.reduceRoot = some d') :
    Prod.Lex Multiset.IsDershowitzMannaLT (· < ·) (normMeasure d') (normMeasure d) := by
  unfold reduceRoot at hd'
  split at hd' <;>
    [skip; skip; skip; skip; skip; skip; skip; skip; (exact absurd hd' (by simp))]
  · -- h_1: impE (impI _ D) E  →  D.subsOne E   (implication β)
    -- reduceRootSubSN: D.isStronglyNormal ∧ E.isStronglyNormal
    -- maximalFormulas (impE (impI G D) E) = {(B→A).complexity} + D.maximalFormulas + E.maximalFormulas
    -- Since D and E are SN, D.maximalFormulas = ∅ and E.maximalFormulas = ∅.
    -- Every element of (D.subsOne E).maximalFormulas is = B.complexity (by subsOne_new_redex_complexity_lt)
    -- and B.complexity < (B→A).complexity.
    rename_i _Γ _A₀ _B D E
    rw [Option.some.injEq] at hd'; subst hd'
    refine Prod.Lex.left _ _ ?_
    simp only [normMeasure, maximalFormulas, conclusionComplexity]
    -- h_subsSN unfolds to D.isStronglyNormal = true ∧ E.isStronglyNormal = true
    rcases h_subsSN with ⟨hD, hE⟩
    -- Provide DM witnesses directly using SN to simplify maximalFormulas
    -- X=∅, Y=(D.subsOne E).maximalFormulas, Z={(_B→A).complexity}
    -- M = (D.subsOne E).maximalFormulas = ∅ + Y, N = {(_B→A).complexity} + D.maximalFormulas + E.maximalFormulas = ∅ + Z
    refine ⟨∅, (D.subsOne E).maximalFormulas,
           {(_B → A).complexity} + D.maximalFormulas + E.maximalFormulas,
           by simp,
           by simp, by simp, ?_⟩
    intro y hy
    refine ⟨(_B → A).complexity, by simp, ?_⟩
    -- y ∈ (D.subsOne E).maximalFormulas; D.maximalFormulas = ∅; so y is new
    rcases subsOne_new_redex_complexity_lt D E hy (by simp [maximalFormulas_sn_eq_zero D hD]) with hkE | rfl
    · -- y ∈ E.maximalFormulas but E.maximalFormulas = ∅
      simp [maximalFormulas_sn_eq_zero E hE] at hkE
    · -- y = _B.complexity; need _B.complexity < (_B → A).complexity
      simp only [Proposition.complexity]; omega
  · -- h_2: andE1 _ (andI _ D₁ D₂)  →  D₁   (conjunction β)
    rw [Option.some.injEq] at hd'; subst hd'
    refine Prod.Lex.left _ _ ?_
    simp only [normMeasure, maximalFormulas, conclusionComplexity]
    exact Multiset.isDershowitzMannaLT_cons_add
  · -- h_3: andE2 _ (andI _ D₁ D₂)  →  D₂   (conjunction β, right projection)
    -- Goal after simp: D₂ < {c} + (D₁ + D₂), use isDershowitzMannaLT_cons_add'
    rw [Option.some.injEq] at hd'; subst hd'
    refine Prod.Lex.left _ _ ?_
    simp only [normMeasure, maximalFormulas, conclusionComplexity]
    exact Multiset.isDershowitzMannaLT_cons_add'
  · -- h_4: orE _ (orI1 _ D) DA _  →  DA.subsOne D   (disjunction β)
    -- reduceRootSubSN: D_or.isStronglyNormal ∧ DA.isStronglyNormal
    rename_i _G' _x _Aor _Bor D_or DA DB_or
    rw [Option.some.injEq] at hd'; subst hd'
    refine Prod.Lex.left _ _ ?_
    simp only [normMeasure, maximalFormulas, conclusionComplexity]
    rcases h_subsSN with ⟨hD, hDA⟩
    -- DM witnesses: X=∅, Y=LHS, Z=full RHS (with D_or.mf and DA.mf still present)
    refine ⟨∅, (DA.subsOne D_or).maximalFormulas,
           {(_Aor ∨ _Bor).complexity} + D_or.maximalFormulas + DA.maximalFormulas + DB_or.maximalFormulas,
           by simp,
           by simp, by simp, ?_⟩
    intro y hy
    refine ⟨(_Aor ∨ _Bor).complexity, by simp, ?_⟩
    rcases subsOne_new_redex_complexity_lt _ _ hy (by simp [maximalFormulas_sn_eq_zero _ hDA]) with hkE | rfl
    · simp [maximalFormulas_sn_eq_zero _ hD] at hkE
    · simp only [Proposition.complexity]; omega
  · -- h_5: orE _ (orI2 _ D) _ DB  →  DB.subsOne D
    -- reduceRootSubSN: D_or.isStronglyNormal ∧ DB.isStronglyNormal
    rename_i _G' _x _Aor _Bor D_or DA_or DB
    rw [Option.some.injEq] at hd'; subst hd'
    refine Prod.Lex.left _ _ ?_
    simp only [normMeasure, maximalFormulas, conclusionComplexity]
    rcases h_subsSN with ⟨hD, hDB⟩
    refine ⟨∅, (DB.subsOne D_or).maximalFormulas,
           {(_Aor ∨ _Bor).complexity} + D_or.maximalFormulas + DA_or.maximalFormulas + DB.maximalFormulas,
           by simp,
           by simp, by simp, ?_⟩
    intro y hy
    refine ⟨(_Aor ∨ _Bor).complexity, by simp, ?_⟩
    rcases subsOne_new_redex_complexity_lt _ _ hy (by simp [maximalFormulas_sn_eq_zero _ hDB]) with hkE | rfl
    · simp [maximalFormulas_sn_eq_zero _ hD] at hkE
    · simp only [Proposition.complexity]; omega
  · -- h_6: andE1 G (orE _ D DA DB)  →  orE G D (andE1 DA) (andE1 DB)   (commuting)
    -- maximalFormulas is preserved (equality); commutingSum strictly decreases
    rename_i _Gp _xp Dcc DAcc DBcc
    rw [Option.some.injEq] at hd'; subst hd'
    rcases h_subsSN with ⟨hA, hB⟩
    show Prod.Lex _ _ (_, _) (_, _)
    -- Key: (andE1 _ DA).maximalFormulas = DA.maximalFormulas when DA is SN (not andI, not orE)
    have hDA_mf : (andE1 _ DAcc).maximalFormulas = DAcc.maximalFormulas := by
      cases DAcc <;>
        simp only [isStronglyNormal, maximalFormulas] at * <;>
        first | exact absurd hA (by decide) | rfl
    have hDB_mf : (andE1 _ DBcc).maximalFormulas = DBcc.maximalFormulas := by
      cases DBcc <;>
        simp only [isStronglyNormal, maximalFormulas] at * <;>
        first | exact absurd hB (by decide) | rfl
    -- Key: (andE1 _ DA).commutingSum = DA.commutingSum when DA is SN (not orE)
    have hDA_cs : (andE1 _ DAcc).commutingSum = DAcc.commutingSum := by
      cases DAcc <;>
        simp only [isStronglyNormal, commutingSum] at * <;>
        first | exact absurd hA (by decide) | rfl
    have hDB_cs : (andE1 _ DBcc).commutingSum = DBcc.commutingSum := by
      cases DBcc <;>
        simp only [isStronglyNormal, commutingSum] at * <;>
        first | exact absurd hB (by decide) | rfl
    rw [show (andE1 G (orE G Dcc DAcc DBcc)).maximalFormulas
          = (orE G Dcc (andE1 _ DAcc) (andE1 _ DBcc)).maximalFormulas from by
        cases Dcc <;> simp_all [maximalFormulas, hDA_mf, hDB_mf]]
    refine Prod.Lex.right _ ?_
    -- Goal: commutingSum (orE Dcc (andE1 DAcc) (andE1 DBcc)) < commutingSum (andE1 (orE Dcc DAcc DBcc))
    -- cases Dcc to unfold commutingSum, then use hDA_cs/hDB_cs
    cases Dcc <;> simp_all [commutingSum, nodeCount, hDA_cs, hDB_cs] <;> omega
  · -- h_7: andE2 G (orE _ D DA DB)  →  orE G D (andE2 DA) (andE2 DB)
    rename_i _Gp _xp Dcc DAcc DBcc
    rw [Option.some.injEq] at hd'; subst hd'
    rcases h_subsSN with ⟨hA, hB⟩
    show Prod.Lex _ _ (_, _) (_, _)
    -- When DAcc is SN under andE2 (not andI, not orE), andE2's maximalFormulas = DAcc's
    have hDA_mf : (andE2 _ DAcc).maximalFormulas = DAcc.maximalFormulas := by
      cases DAcc <;>
        simp only [isStronglyNormal, maximalFormulas] at * <;>
        first | exact absurd hA (by decide) | rfl
    have hDB_mf : (andE2 _ DBcc).maximalFormulas = DBcc.maximalFormulas := by
      cases DBcc <;>
        simp only [isStronglyNormal, maximalFormulas] at * <;>
        first | exact absurd hB (by decide) | rfl
    have hDA_cs : (andE2 _ DAcc).commutingSum = DAcc.commutingSum := by
      cases DAcc <;>
        simp only [isStronglyNormal, commutingSum] at * <;>
        first | exact absurd hA (by decide) | rfl
    have hDB_cs : (andE2 _ DBcc).commutingSum = DBcc.commutingSum := by
      cases DBcc <;>
        simp only [isStronglyNormal, commutingSum] at * <;>
        first | exact absurd hB (by decide) | rfl
    rw [show (andE2 G (orE G Dcc DAcc DBcc)).maximalFormulas
          = (orE G Dcc (andE2 _ DAcc) (andE2 _ DBcc)).maximalFormulas from by
        cases Dcc <;> simp_all [maximalFormulas, hDA_mf, hDB_mf]]
    refine Prod.Lex.right _ ?_
    cases Dcc <;> simp_all [commutingSum, nodeCount, hDA_cs, hDB_cs] <;> omega
  · -- h_8: impE (orE G D DA DB) E  →  orE G D (impE DA E') (impE DB E')
    -- reduceRootSubSN gives:
    --   hA : (DAcc.impE (weakCtx ⋯ Ecc)).isStronglyNormal = true
    --   hB : (DBcc.impE (weakCtx ⋯ Ecc)).isStronglyNormal = true
    -- Since DAcc is SN and NOT impI or orE, hA forces (weakCtx ⋯ Ecc).isStronglyNormal.
    -- Hence: (weakCtx ⋯ Ecc).maximalFormulas = ∅ (maximalFormulas_sn_eq_zero + _weakCtx)
    --         (weakCtx ⋯ Ecc).commutingSum = 0   (commutingSum_sn_eq_zero  + _weakCtx)
    -- With Ecc's extra copies gone, maximalFormulas equality holds and commutingSum decreases
    -- by (orE G Dcc DAcc DBcc).nodeCount ≥ 1.
    rename_i _Gp _xp _Aimp _Aor _Bor D_or DA_or DB_or E_or
    rw [Option.some.injEq] at hd'; subst hd'
    rcases h_subsSN with ⟨hA, hB⟩
    show Prod.Lex _ _ (_, _) (_, _)
    -- Extract (weakCtx E_or).isStronglyNormal from hA by cases on DA_or.
    -- DA_or = impI/orE gives (impE ... ...).isStronglyNormal = false → hA : false = true.
    -- All other constructors give hA as a conjunction; the second component is E's SN.
    have hE_sn : (E_or.weakCtx (Finset.subset_insert _Aor G)).isStronglyNormal = true := by
      cases DA_or <;>
        simp only [isStronglyNormal, Bool.and_eq_true] at hA <;>
        first | exact absurd hA (by decide) | exact hA.2 | exact hA
    -- E_or.maximalFormulas = ∅ and E_or.commutingSum = 0 (weakCtx invariance + SN)
    have hE_mf : E_or.maximalFormulas = ∅ := by
      have h := maximalFormulas_sn_eq_zero _ hE_sn
      rw [maximalFormulas_weakCtx] at h; exact h
    have hE_cs : E_or.commutingSum = 0 := by
      have h := commutingSum_sn_eq_zero _ hE_sn
      rw [commutingSum_weakCtx] at h; exact h
    -- maximalFormulas of (impE DA_or (weakCtx E_or)) = DA_or.maximalFormulas:
    -- impI/orE excluded by hA; for others, (weakCtx E_or).maximalFormulas = ∅ drops out
    have hDA_mf : (DA_or.impE (E_or.weakCtx (Finset.subset_insert _ _))).maximalFormulas
                  = DA_or.maximalFormulas := by
      cases DA_or <;>
        simp only [isStronglyNormal, maximalFormulas, maximalFormulas_weakCtx, hE_mf] at * <;>
        first | exact absurd hA (by decide) | simp
    have hDB_mf : (DB_or.impE (E_or.weakCtx (Finset.subset_insert _ _))).maximalFormulas
                  = DB_or.maximalFormulas := by
      cases DB_or <;>
        simp only [isStronglyNormal, maximalFormulas, maximalFormulas_weakCtx, hE_mf] at * <;>
        first | exact absurd hB (by decide) | simp
    -- commutingSum of (impE DA_or (weakCtx E_or)) = DA_or.commutingSum:
    -- orE excluded by hA; for others, (weakCtx E_or).commutingSum = 0 drops out
    have hDA_cs : (DA_or.impE (E_or.weakCtx (Finset.subset_insert _ _))).commutingSum
                  = DA_or.commutingSum := by
      cases DA_or <;>
        simp only [isStronglyNormal, commutingSum, commutingSum_weakCtx, hE_cs] at * <;>
        first | exact absurd hA (by decide) | omega
    have hDB_cs : (DB_or.impE (E_or.weakCtx (Finset.subset_insert _ _))).commutingSum
                  = DB_or.commutingSum := by
      cases DB_or <;>
        simp only [isStronglyNormal, commutingSum, commutingSum_weakCtx, hE_cs] at * <;>
        first | exact absurd hB (by decide) | omega
    -- maximalFormulas equality: duplicated E copies cancel (hE_mf makes them ∅)
    rw [show ((orE G D_or DA_or DB_or).impE E_or).maximalFormulas
          = (orE G D_or
              (DA_or.impE (E_or.weakCtx (Finset.subset_insert _Aor G)))
              (DB_or.impE (E_or.weakCtx (Finset.subset_insert _Bor G)))).maximalFormulas from by
        cases D_or <;> simp_all [maximalFormulas, hDA_mf, hDB_mf, hE_mf]]
    refine Prod.Lex.right _ ?_
    -- commutingSum strictly decreases by (orE G D_or DA_or DB_or).nodeCount ≥ 1
    cases D_or <;> simp_all [commutingSum, nodeCount, hDA_cs, hDB_cs, hE_cs] <;> omega

/-- Theory and context weakening preserves `isStronglyNormal`. -/
private theorem Theory.Derivation.isStronglyNormal_weak {T T' : Theory Atom} {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hTheory : T ⊆ T') (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weak hTheory hCtx).isStronglyNormal = D.isStronglyNormal := by
  induction D generalizing T' Δ with
  | ax => rfl
  | ass => rfl
  | andI G D₁ D₂ ih₁ ih₂ =>
    simp only [Theory.Derivation.weak, isStronglyNormal, ih₁, ih₂]
  | andE1 G D ih =>
    simp only [isStronglyNormal] at ih ⊢
    cases D <;> simp_all [Theory.Derivation.weak, isStronglyNormal]
  | andE2 G D ih =>
    simp only [isStronglyNormal] at ih ⊢
    cases D <;> simp_all [Theory.Derivation.weak, isStronglyNormal]
  | orI1 G D ih => simp only [Theory.Derivation.weak, isStronglyNormal, ih]
  | orI2 G D ih => simp only [Theory.Derivation.weak, isStronglyNormal, ih]
  | orE G D DA DB ih ihA ihB =>
    simp only [isStronglyNormal] at ih ⊢
    cases D <;>
      simp_all [Theory.Derivation.weak, isStronglyNormal]
  | impI G D ih => simp only [Theory.Derivation.weak, isStronglyNormal, ih]
  | impE D E ih ihE =>
    simp only [isStronglyNormal] at ih ⊢
    cases D <;> simp_all [Theory.Derivation.weak, isStronglyNormal]

/-- Context weakening preserves `isStronglyNormal` (corollary of `isStronglyNormal_weak`). -/
private theorem Theory.Derivation.isStronglyNormal_weakCtx {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weakCtx hCtx).isStronglyNormal = D.isStronglyNormal :=
  D.isStronglyNormal_weak Set.Subset.rfl hCtx

/-- Given a strongly-normal derivation `e : G ⊢ A ∧ B`, produce a strongly-normal `G ⊢ A`.
Structural recursion on `e`: at an `andI` leaf project the first component; at an `orE` node
push `andE1` into both branches. -/
private def Theory.Derivation.snAndE1Form {G : Ctx Atom} {A B : Proposition Atom}
    (e : T.Derivation G (A ∧ B)) (he : e.isStronglyNormal = true) :
    {d : T.Derivation G A // d.isStronglyNormal = true} :=
  match e, he with
  | andI _ X _, he => ⟨X, by simp only [isStronglyNormal, Bool.and_eq_true] at he; exact he.1⟩
  | orE G D DA DB, he => by
      have hD  : D.isStronglyNormal  = true := by cases D <;> simp_all [isStronglyNormal]
      have hDA : DA.isStronglyNormal = true := by cases D <;> simp_all [isStronglyNormal]
      have hDB : DB.isStronglyNormal = true := by cases D <;> simp_all [isStronglyNormal]
      refine ⟨orE G D (snAndE1Form DA hDA).1 (snAndE1Form DB hDB).1, ?_⟩
      have hX := (snAndE1Form DA hDA).2
      have hY := (snAndE1Form DB hDB).2
      cases D <;> simp_all [isStronglyNormal, isOrERoot, isIntroRoot]
  | ax h,   _  => ⟨andE1 _ (ax h),  rfl⟩
  | ass h,  _  => ⟨andE1 _ (ass h), rfl⟩
  | andE1 _ D', he => ⟨andE1 _ (andE1 _ D'), by simpa [isStronglyNormal] using he⟩
  | andE2 _ D', he => ⟨andE1 _ (andE2 _ D'), by simpa [isStronglyNormal] using he⟩
  | impE D' E', he => ⟨andE1 _ (impE D' E'), by simpa [isStronglyNormal] using he⟩

/-- Given a strongly-normal derivation `e : G ⊢ A ∧ B`, produce a strongly-normal `G ⊢ B`.
Symmetric to `snAndE1Form`: at an `andI` leaf project the second component. -/
private def Theory.Derivation.snAndE2Form {G : Ctx Atom} {A B : Proposition Atom}
    (e : T.Derivation G (A ∧ B)) (he : e.isStronglyNormal = true) :
    {d : T.Derivation G B // d.isStronglyNormal = true} :=
  match e, he with
  | andI _ _ Y, he => ⟨Y, by simp only [isStronglyNormal, Bool.and_eq_true] at he; exact he.2⟩
  | orE G D DA DB, he => by
      have hD  : D.isStronglyNormal  = true := by cases D <;> simp_all [isStronglyNormal]
      have hDA : DA.isStronglyNormal = true := by cases D <;> simp_all [isStronglyNormal]
      have hDB : DB.isStronglyNormal = true := by cases D <;> simp_all [isStronglyNormal]
      refine ⟨orE G D (snAndE2Form DA hDA).1 (snAndE2Form DB hDB).1, ?_⟩
      have hX := (snAndE2Form DA hDA).2
      have hY := (snAndE2Form DB hDB).2
      cases D <;> simp_all [isStronglyNormal, isOrERoot, isIntroRoot]
  | ax h,   _  => ⟨andE2 _ (ax h),  rfl⟩
  | ass h,  _  => ⟨andE2 _ (ass h), rfl⟩
  | andE1 _ D', he => ⟨andE2 _ (andE1 _ D'), by simpa [isStronglyNormal] using he⟩
  | andE2 _ D', he => ⟨andE2 _ (andE2 _ D'), by simpa [isStronglyNormal] using he⟩
  | impE D' E', he => ⟨andE2 _ (impE D' E'), by simpa [isStronglyNormal] using he⟩

/-- Head-behaviour lemma for `snAndE1Form`: if the output is intro-or-`orE`-headed, then the
input `e` was already intro-or-`orE`-headed. The only way `snAndE1Form` produces a non-neutral
head is at an `andI` leaf (output is the first projection, possibly intro-headed) or an `orE`
node (output is `orE`-headed); in both the input head is `andI`/`orE`. Neutral inputs produce an
`andE1`-headed (neutral) output. -/
private lemma Theory.Derivation.snAndE1Form_head {G : Ctx Atom} {A B : Proposition Atom}
    (e : T.Derivation G (A ∧ B)) (he : e.isStronglyNormal = true) :
    ((snAndE1Form e he).1.isIntroRoot = true ∨ (snAndE1Form e he).1.isOrERoot = true) →
      (e.isIntroRoot = true ∨ e.isOrERoot = true) := by
  cases e <;> simp_all [snAndE1Form, isIntroRoot, isOrERoot]

/-- Head-behaviour lemma for `snAndE2Form` (symmetric to `snAndE1Form_head`). -/
private lemma Theory.Derivation.snAndE2Form_head {G : Ctx Atom} {A B : Proposition Atom}
    (e : T.Derivation G (A ∧ B)) (he : e.isStronglyNormal = true) :
    ((snAndE2Form e he).1.isIntroRoot = true ∨ (snAndE2Form e he).1.isOrERoot = true) →
      (e.isIntroRoot = true ∨ e.isOrERoot = true) := by
  cases e <;> simp_all [snAndE2Form, isIntroRoot, isOrERoot]

/-- `normalize` produces strongly normal derivations.

Proved via `redexWeight_zero_sn`: the goal reduces to showing `(d.normalize).redexWeight = 0`,
which follows from Prawitz's normalization theorem — the `normalizeAux` function with
`2^d.height` fuel iterates root reductions until the `redexWeight` reaches 0.
The strict decrease at each step (for proper β-redexes via the substitution complexity
argument, for commuting conversions via the elimination-push structure) guarantees termination
within the fuel bound. ([Prawitz1965], Ch. III–IV.) -/
theorem Theory.Derivation.normalize_isStronglyNormal {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) : d.normalize.isStronglyNormal = true := by
  apply redexWeight_zero_sn
  -- Goal: d.normalize.redexWeight = 0
  -- This follows from the normalization theorem: normalize eliminates all redexes
  -- The proof requires induction on redexWeight and fuel simultaneously
  sorry

/-! ## SCRATCH: snImpEForm / snOrEForm / snSubst development -/

private lemma cx_imp_left {A B : Proposition Atom} : A.complexity < (A → B).complexity := by
  simp only [Proposition.complexity]; omega

private lemma cx_imp_right {A B : Proposition Atom} : B.complexity < (A → B).complexity := by
  simp only [Proposition.complexity]; omega

private lemma cx_or_left {A B : Proposition Atom} : A.complexity < (A ∨ B).complexity := by
  simp only [Proposition.complexity]; omega

private lemma cx_or_right {A B : Proposition Atom} : B.complexity < (A ∨ B).complexity := by
  simp only [Proposition.complexity]; omega

private lemma cx_and_left {A B : Proposition Atom} : A.complexity < (A ∧ B).complexity := by
  simp only [Proposition.complexity]; omega

private lemma cx_and_right {A B : Proposition Atom} : B.complexity < (A ∧ B).complexity := by
  simp only [Proposition.complexity]; omega

/-! ### Mutual block: VALIDATED termination measure for L3/L4/L5

RESULT (machine-checked below): the mutual well-founded recursion of `snImpEForm` (L3),
`snOrEForm` (L4), `snSubst` (L5) terminates under the **3-component lexicographic measure**

    (cut-formula complexity, phase, structural size)

where `phase = 0` for the two eliminators and `phase = 1` for `snSubst`, and the cut formula is
`A → B` for `snImpEForm`, `A ∨ B` for `snOrEForm`, and `P` (the substituted hypothesis) for
`snSubst`. Every recursive edge is discharged by `decreasing_by` as follows:

  * eliminator → eliminator (push/commuting, structural on the principal premise): same
    complexity, same phase, strictly smaller `sizeOf` — closed by `decreasing_tactic`.
  * eliminator → snSubst (β-redex, substitute at a PROPER subformula of the cut): first
    component strictly drops (`A.complexity < (A → B).complexity`, etc.) — closed by
    `left; simp [Proposition.complexity]; omega`.
  * snSubst → snSubst (structural on `body`): same complexity, same phase, smaller `sizeOf` —
    closed by `decreasing_tactic`.
  * snSubst → eliminator (re-eliminate a substituted child at an `impE` node): the **HEAD-BOUND**.
    `snSubst`'s `impE` case head-matches `(snSubst D' arg).1`: in the intro-or-orE-headed
    sub-case the carried invariant yields `(type D').complexity ≤ P.complexity`, so the edge
    decreases (`< P` ⇒ first component, `= P` at the bare-variable site ⇒ phase `0 < 1`); in the
    neutral sub-case the result is reassembled as `impE` directly, with no eliminator call.
    This edge is now discharged **sorry-free** via `lex3_of_le_of_lt` and the head invariant.

CLOSED in this dispatch (head-bound termination, no `sorry`):
  - Head-behaviour invariant carried in `snSubst`'s return subtype:
      `body.isIntroRoot = false → ((d.isIntroRoot ∨ d.isOrERoot) → B.complexity ≤ P.complexity)`,
    proven for the `ax/ass/andI/andE1/andE2/impE/orI1/orI2` cases (the head-bound's entire
    dependency cone — neutral implications `ax/ass/andE1/andE2/impE` — is sorry-free).
  - Standalone head-behaviour lemmas `snAndE1Form_head`/`snAndE2Form_head`, complexity
    subformula lemmas `cx_and_left/right`, `sizeOf_impE_left/right`, and the lex lemma
    `lex3_of_le_of_lt`.

CLOSED (this dispatch) — the mutual block L3/L4/L5 is now fully `sorry`-free:
  - `snOrEForm`'s commuting `orE` case (push the elimination into the SN `orE`'s branches,
    re-eliminating via `snOrEForm`).
  - `snSubst`'s `impI` and `orE` cases via the context-reindex cast
    `insert A (insert P G) = insert P (insert A G)` (`Finset.insert_comm`), with cast invariance
    lemmas `isStronglyNormal_cast`/`sizeOf_cast` threading the `sizeOf` equality into
    `decreasing_by` (`rw [sizeOf_cast]; omega`).
  - The carried head invariant was refined with a `body.isOrERoot = false` antecedent (the `orE`
    case's conclusion need not be a subformula of the eliminated disjunction); all consumers
    supply it since an elimination's major premise is never `orE`-headed in a SN derivation.

The `snSubst` head-bound termination obligation is discharged sorry-free via the carried
head-behaviour invariant (see `snSubst` below); the stage-1 scaffolding stubs have been
removed. The structural driver `snForm` (L6) and `exists_stronglyNormal_form` are appended after
the block. The only remaining `sorry` in this file is the pre-existing fuel `sorry` in
`normalize_isStronglyNormal` (copied from `Termination.lean`; the final phase). -/

/-- `sizeOf` of an `impE`'s function premise is smaller than the whole derivation. Proven
outside the mutual block so the termination proof can close the `impE` structural edge by a
cheap `exact` instead of an expensive in-context `simp`/`omega`. -/
private lemma sizeOf_impE_left {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : T.Derivation Γ (A → B)) (E : T.Derivation Γ A) : sizeOf D < sizeOf (D.impE E) := by
  simp only [Cslib.Logic.PL.Theory.Derivation.impE.sizeOf_spec]; omega

/-- `sizeOf` of an `impE`'s argument premise is smaller than the whole derivation. -/
private lemma sizeOf_impE_right {Γ : Ctx Atom} {A B : Proposition Atom}
    (D : T.Derivation Γ (A → B)) (E : T.Derivation Γ A) : sizeOf E < sizeOf (D.impE E) := by
  simp only [Cslib.Logic.PL.Theory.Derivation.impE.sizeOf_spec]; omega

/-- Lexicographic decrease of the 3-component measure when the first component is `≤` and the
second is `<` (the head-bound edge: cut complexity `≤ P` and phase `0 < 1`). Proven standalone
so the `subst` on the equal-first-component case works on plain `ℕ` variables (a `rw` in the
`decreasing_by` context fails with a dependent-motive error). -/
private lemma lex3_of_le_of_lt {a a' b b' c c' : ℕ} (ha : a ≤ a') (hb : b < b') :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a, b, c) (a', b', c') := by
  rcases lt_or_eq_of_le ha with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ (Prod.Lex.left _ _ hb)

/-- Casting a derivation along a context equality preserves `isStronglyNormal` (the predicate
depends only on the derivation tree, not on the context index). Used to reindex the binder
contexts of `impI`/`orE` subderivations (`insert A (insert P G) = insert P (insert A G)`) so the
substituted hypothesis `P` sits at the front for the `snSubst` recursive call. -/
private lemma isStronglyNormal_cast {Γ Γ₂ : Ctx Atom} {A : Proposition Atom} (h : Γ = Γ₂)
    (D : T.Derivation Γ A) : (h ▸ D).isStronglyNormal = D.isStronglyNormal := by subst h; rfl

/-- Casting a derivation along a context equality preserves `sizeOf` (the cast is a no-op on the
tree). Lets the `snSubst` termination proof close the `impI`/`orE` binder edges by rewriting the
cast away before the structural `sizeOf` comparison. -/
private lemma sizeOf_cast {Γ Γ₂ : Ctx Atom} {A : Proposition Atom} (h : Γ = Γ₂)
    (D : T.Derivation Γ A) : sizeOf (h ▸ D) = sizeOf D := by subst h; rfl

-- The mutual well-founded recursion `snImpEForm`/`snOrEForm`/`snSubst` with the carried
-- head-behaviour invariant produces a large equation-compiler goal; raise the heartbeat
-- limit so the (sorry-free) termination proof elaborates within budget.
set_option maxHeartbeats 2000000 in
mutual

/-- L3: smart implication eliminator. Measure: ((A→B).complexity, 0, sizeOf f). -/
private def Theory.Derivation.snImpEForm {G : Ctx Atom} {A B : Proposition Atom}
    (f : T.Derivation G (A → B)) (hf : f.isStronglyNormal = true)
    (a : T.Derivation G A) (ha : a.isStronglyNormal = true) :
    {d : T.Derivation G B // d.isStronglyNormal = true} :=
  match f, hf with
  | .impI _ body, hf =>
      have hbody : body.isStronglyNormal = true := by simpa [isStronglyNormal] using hf
      let r := snSubst body hbody a ha
      ⟨r.1, r.2.1⟩
  | .orE G D DA DB, hf => by
      have hDA : DA.isStronglyNormal = true := by cases D <;> simp_all [isStronglyNormal]
      have hDB : DB.isStronglyNormal = true := by cases D <;> simp_all [isStronglyNormal]
      let xA := snImpEForm DA hDA (a.weakCtx (Finset.subset_insert _ _))
        (by rw [isStronglyNormal_weakCtx]; exact ha)
      let xB := snImpEForm DB hDB (a.weakCtx (Finset.subset_insert _ _))
        (by rw [isStronglyNormal_weakCtx]; exact ha)
      refine ⟨orE G D xA.1 xB.1, ?_⟩
      have hX := xA.2
      have hY := xB.2
      cases D <;> simp_all [isStronglyNormal]
  | .ax h,   _  => ⟨Derivation.impE (ax h) a,   by simp [isStronglyNormal]; exact ha⟩
  | .ass h,  _  => ⟨Derivation.impE (ass h) a,  by simp [isStronglyNormal]; exact ha⟩
  | .andE1 _ D', hf => ⟨Derivation.impE (andE1 _ D') a, by
      simp only [isStronglyNormal, Bool.and_eq_true]; exact ⟨hf, ha⟩⟩
  | .andE2 _ D', hf => ⟨Derivation.impE (andE2 _ D') a, by
      simp only [isStronglyNormal, Bool.and_eq_true]; exact ⟨hf, ha⟩⟩
  | .impE D' E', hf => ⟨Derivation.impE (Derivation.impE D' E') a, by
      simp only [isStronglyNormal, Bool.and_eq_true]; exact ⟨hf, ha⟩⟩
  termination_by ((A → B).complexity, 0, sizeOf f)
  decreasing_by all_goals (simp_wf; first | (left; simp [Proposition.complexity]; omega) | (right; omega))

/-- L4: smart disjunction eliminator. Measure: ((A∨B).complexity, 0, sizeOf D). -/
private def Theory.Derivation.snOrEForm {G : Ctx Atom} {A B C : Proposition Atom}
    (D : T.Derivation G (A ∨ B)) (hD : D.isStronglyNormal = true)
    (DA : T.Derivation (insert A G) C) (hDA : DA.isStronglyNormal = true)
    (DB : T.Derivation (insert B G) C) (hDB : DB.isStronglyNormal = true) :
    {d : T.Derivation G C // d.isStronglyNormal = true} :=
  match D, hD with
  | .orI1 _ d0, hD =>
      have hd0 : d0.isStronglyNormal = true := by simpa [isStronglyNormal] using hD
      let r := snSubst DA hDA d0 hd0
      ⟨r.1, r.2.1⟩
  | .orI2 _ d0, hD =>
      have hd0 : d0.isStronglyNormal = true := by simpa [isStronglyNormal] using hD
      let r := snSubst DB hDB d0 hd0
      ⟨r.1, r.2.1⟩
  | .orE G' D' DA' DB', hD => by
      -- commuting conversion: push the outer `orE _ _ DA DB` elimination into the SN `orE`'s
      -- branches `DA'`/`DB'` (re-eliminating via `snOrEForm` to renormalize the new redex).
      have hD'  : D'.isStronglyNormal  = true := by cases D' <;> simp_all [isStronglyNormal]
      have hDA' : DA'.isStronglyNormal = true := by cases D' <;> simp_all [isStronglyNormal]
      have hDB' : DB'.isStronglyNormal = true := by cases D' <;> simp_all [isStronglyNormal]
      let xA := snOrEForm DA' hDA'
        (DA.weakCtx (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        (by rw [isStronglyNormal_weakCtx]; exact hDA)
        (DB.weakCtx (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        (by rw [isStronglyNormal_weakCtx]; exact hDB)
      let xB := snOrEForm DB' hDB'
        (DA.weakCtx (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        (by rw [isStronglyNormal_weakCtx]; exact hDA)
        (DB.weakCtx (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        (by rw [isStronglyNormal_weakCtx]; exact hDB)
      refine ⟨orE G' D' xA.1 xB.1, ?_⟩
      have hX := xA.2
      have hY := xB.2
      cases D' <;> simp_all [isStronglyNormal]
  | .ax h, _ => ⟨orE G (ax h) DA DB, by simp_all [isStronglyNormal]⟩
  | .ass h, _ => ⟨orE G (ass h) DA DB, by simp_all [isStronglyNormal]⟩
  | .andE1 _ D', hD => ⟨orE G (andE1 _ D') DA DB, by
      simp only [isStronglyNormal, Bool.and_eq_true] at hD ⊢; exact ⟨⟨hD, hDA⟩, hDB⟩⟩
  | .andE2 _ D', hD => ⟨orE G (andE2 _ D') DA DB, by
      simp only [isStronglyNormal, Bool.and_eq_true] at hD ⊢; exact ⟨⟨hD, hDA⟩, hDB⟩⟩
  | .impE D' E', hD => ⟨orE G (Derivation.impE D' E') DA DB, by
      simp only [isStronglyNormal, Bool.and_eq_true] at hD ⊢; exact ⟨⟨hD, hDA⟩, hDB⟩⟩
  termination_by ((A ∨ B).complexity, 0, sizeOf D)
  decreasing_by all_goals (simp_wf; first | (left; simp [Proposition.complexity]; omega) | (right; omega))

/-- L5: substitution-normalization. Measure: `(P.complexity, 1, sizeOf body)`.

The return subtype carries, beyond strong normality, the **head-behaviour invariant**

    body.isIntroRoot = false → body.isOrERoot = false →
      (d.isIntroRoot = true ∨ d.isOrERoot = true) → B.complexity ≤ P.complexity

i.e. if the input `body` is a *neutral elimination* (neither intro- nor `orE`-headed) and the
substituted output became intro-or-`orE`-headed, then the substituted variable was on `body`'s
elimination spine and the conclusion `B` is a subformula of the cut `P`. This is exactly what
discharges the head-bound termination obligation at the `impE`/`orE` re-elimination edge (the
`snSubst → snImpEForm`/`snOrEForm` call). The `body.isOrERoot = false` antecedent is required for
the `orE` case (whose conclusion `B` need not be a subformula of the eliminated disjunction); it
is always available at the consumers because in a strongly-normal derivation an elimination's
major premise is never `orE`-headed (that would be a commuting conversion). -/
private def Theory.Derivation.snSubst {P B : Proposition Atom} {G : Ctx Atom}
    (body : T.Derivation (insert P G) B) (hbody : body.isStronglyNormal = true)
    (arg : T.Derivation G P) (harg : arg.isStronglyNormal = true) :
    {d : T.Derivation G B //
      d.isStronglyNormal = true ∧
      (body.isIntroRoot = false → body.isOrERoot = false →
        (d.isIntroRoot = true ∨ d.isOrERoot = true) → B.complexity ≤ P.complexity)} :=
  match body, hbody with
  | .ax h, _ => ⟨ax h, rfl, by intro _ _ hor; simp [isIntroRoot, isOrERoot] at hor⟩
  | .ass h, _ => by
      by_cases hBP : B = P
      · subst hBP; exact ⟨arg, harg, by intro _ _ _; exact le_refl _⟩
      · exact ⟨ass ((Finset.mem_insert.mp h).resolve_left hBP), rfl,
          by intro _ _ hor; simp [isIntroRoot, isOrERoot] at hor⟩
  | .andI _ X Y, hbd =>
      have hbd' : X.isStronglyNormal = true ∧ Y.isStronglyNormal = true := by
        simpa only [isStronglyNormal, Bool.and_eq_true] using hbd
      let sx := snSubst X hbd'.1 arg harg
      let sy := snSubst Y hbd'.2 arg harg
      ⟨andI _ sx.1 sy.1, by
        refine ⟨?_, ?_⟩
        · simp only [isStronglyNormal, Bool.and_eq_true]; exact ⟨sx.2.1, sy.2.1⟩
        · intro hni _ _; simp [isIntroRoot] at hni⟩
  | .orI1 _ d0, hbd =>
      have hd0 : d0.isStronglyNormal = true := by simpa only [isStronglyNormal] using hbd
      let s := snSubst d0 hd0 arg harg
      ⟨orI1 _ s.1, by
        refine ⟨?_, ?_⟩
        · simpa only [isStronglyNormal] using s.2.1
        · intro hni _ _; simp [isIntroRoot] at hni⟩
  | .orI2 _ d0, hbd =>
      have hd0 : d0.isStronglyNormal = true := by simpa only [isStronglyNormal] using hbd
      let s := snSubst d0 hd0 arg harg
      ⟨orI2 _ s.1, by
        refine ⟨?_, ?_⟩
        · simpa only [isStronglyNormal] using s.2.1
        · intro hni _ _; simp [isIntroRoot] at hni⟩
  | .andE1 _ D', hbd =>
      have hD'sn : D'.isStronglyNormal = true := by cases D' <;> simp_all [isStronglyNormal]
      have hD'ni : D'.isIntroRoot = false := by
        cases D' <;> simp_all [isStronglyNormal, isIntroRoot]
      have hD'no : D'.isOrERoot = false := by
        cases D' <;> simp_all [isStronglyNormal, isOrERoot]
      let e := snSubst D' hD'sn arg harg
      let s := snAndE1Form e.1 e.2.1
      ⟨s.1, s.2, by
        intro _ _ hd
        have hee := snAndE1Form_head e.1 e.2.1 hd
        have hle := e.2.2 hD'ni hD'no hee
        exact le_trans (le_of_lt cx_and_left) hle⟩
  | .andE2 _ D', hbd =>
      have hD'sn : D'.isStronglyNormal = true := by cases D' <;> simp_all [isStronglyNormal]
      have hD'ni : D'.isIntroRoot = false := by
        cases D' <;> simp_all [isStronglyNormal, isIntroRoot]
      have hD'no : D'.isOrERoot = false := by
        cases D' <;> simp_all [isStronglyNormal, isOrERoot]
      let e := snSubst D' hD'sn arg harg
      let s := snAndE2Form e.1 e.2.1
      ⟨s.1, s.2, by
        intro _ _ hd
        have hee := snAndE2Form_head e.1 e.2.1 hd
        have hle := e.2.2 hD'ni hD'no hee
        exact le_trans (le_of_lt cx_and_right) hle⟩
  | .impE D' E', hbd =>
      have hD'sn : D'.isStronglyNormal = true := by cases D' <;> simp_all [isStronglyNormal]
      have hE'sn : E'.isStronglyNormal = true := by cases D' <;> simp_all [isStronglyNormal]
      have hD'ni : D'.isIntroRoot = false := by
        cases D' <;> simp_all [isStronglyNormal, isIntroRoot]
      have hD'no : D'.isOrERoot = false := by
        cases D' <;> simp_all [isStronglyNormal, isOrERoot]
      let d' := snSubst D' hD'sn arg harg
      let e' := snSubst E' hE'sn arg harg
      if h : d'.1.isIntroRoot = true ∨ d'.1.isOrERoot = true then
        have hle := d'.2.2 hD'ni hD'no h
        let r := snImpEForm d'.1 d'.2.1 e'.1 e'.2.1
        ⟨r.1, r.2, by intro _ _ _; exact le_trans (le_of_lt cx_imp_right) hle⟩
      else
        ⟨impE d'.1 e'.1, by
          have hi : d'.1.isIntroRoot = false := by
            cases hb : d'.1.isIntroRoot
            · rfl
            · exact absurd (Or.inl hb) h
          have ho : d'.1.isOrERoot = false := by
            cases hb : d'.1.isOrERoot
            · rfl
            · exact absurd (Or.inr hb) h
          have hsnD := d'.2.1
          have hsnE := e'.2.1
          refine ⟨?_, ?_⟩
          · cases hx : d'.1 <;> simp_all [isStronglyNormal, isIntroRoot, isOrERoot]
          · intro _ _ hor; simp [isIntroRoot, isOrERoot] at hor⟩
  | .impI (A := A0) (B := B0) _ bd, hbd =>
      -- `body = impI bd : insert P G ⊢ (A0 → B0)`; substitute `arg` for `P` under the binder by
      -- reindexing `bd`'s context `insert A0 (insert P G) = insert P (insert A0 G)` (P to front),
      -- weakening `arg` into `insert A0 G`, and recursing; reassemble with `impI`.
      have hbd0 : bd.isStronglyNormal = true := by simpa only [isStronglyNormal] using hbd
      let bd' : T.Derivation (insert P (insert A0 G)) B0 := Finset.insert_comm A0 P G ▸ bd
      have hbd' : bd'.isStronglyNormal = true := by
        show (Finset.insert_comm A0 P G ▸ bd).isStronglyNormal = true
        rw [isStronglyNormal_cast]; exact hbd0
      let s := snSubst bd' hbd' (arg.weakCtx (Finset.subset_insert _ _))
        (by rw [isStronglyNormal_weakCtx]; exact harg)
      ⟨impI _ s.1, by
        refine ⟨?_, ?_⟩
        · simpa only [isStronglyNormal] using s.2.1
        · intro hni _ _; simp [isIntroRoot] at hni⟩
  | .orE (A := A0) (B := B0) _ D' DA' DB', hbd =>
      -- `body = orE D' DA' DB' : insert P G ⊢ B`, strongly normal ⇒ major premise `D'` is neutral
      -- and not `orE`-headed. Substitute `arg` for `P` in `D'` and (after reindexing the binder
      -- contexts `insert A0/B0 (insert P G) = insert P (insert A0/B0 G)`) in the branches; then
      -- head-match the substituted major premise `sd'`: if it became intro-or-`orE`-headed,
      -- re-eliminate via `snOrEForm` (head-bound edge); otherwise reassemble `orE` directly.
      have hD'sn  : D'.isStronglyNormal  = true := by cases D' <;> simp_all [isStronglyNormal]
      have hDA'sn : DA'.isStronglyNormal = true := by cases D' <;> simp_all [isStronglyNormal]
      have hDB'sn : DB'.isStronglyNormal = true := by cases D' <;> simp_all [isStronglyNormal]
      have hD'ni : D'.isIntroRoot = false := by
        cases D' <;> simp_all [isStronglyNormal, isIntroRoot]
      have hD'no : D'.isOrERoot = false := by
        cases D' <;> simp_all [isStronglyNormal, isOrERoot]
      let sd' := snSubst D' hD'sn arg harg
      let dA' : T.Derivation (insert P (insert A0 G)) B := Finset.insert_comm A0 P G ▸ DA'
      have hdA' : dA'.isStronglyNormal = true := by
        show (Finset.insert_comm A0 P G ▸ DA').isStronglyNormal = true
        rw [isStronglyNormal_cast]; exact hDA'sn
      let sA := snSubst dA' hdA' (arg.weakCtx (Finset.subset_insert _ _))
        (by rw [isStronglyNormal_weakCtx]; exact harg)
      let dB' : T.Derivation (insert P (insert B0 G)) B := Finset.insert_comm B0 P G ▸ DB'
      have hdB' : dB'.isStronglyNormal = true := by
        show (Finset.insert_comm B0 P G ▸ DB').isStronglyNormal = true
        rw [isStronglyNormal_cast]; exact hDB'sn
      let sB := snSubst dB' hdB' (arg.weakCtx (Finset.subset_insert _ _))
        (by rw [isStronglyNormal_weakCtx]; exact harg)
      if h : sd'.1.isIntroRoot = true ∨ sd'.1.isOrERoot = true then
        have hle := sd'.2.2 hD'ni hD'no h
        let r := snOrEForm sd'.1 sd'.2.1 sA.1 sA.2.1 sB.1 sB.2.1
        ⟨r.1, r.2, by intro _ hno _; simp [isOrERoot] at hno⟩
      else
        ⟨orE _ sd'.1 sA.1 sB.1, by
          have hi : sd'.1.isIntroRoot = false := by
            cases hb : sd'.1.isIntroRoot
            · rfl
            · exact absurd (Or.inl hb) h
          have ho : sd'.1.isOrERoot = false := by
            cases hb : sd'.1.isOrERoot
            · rfl
            · exact absurd (Or.inr hb) h
          have hsnD := sd'.2.1
          have hsnA := sA.2.1
          have hsnB := sB.2.1
          refine ⟨?_, ?_⟩
          · cases hx : sd'.1 <;> simp_all [isStronglyNormal, isIntroRoot, isOrERoot]
          · intro _ hno _; simp [isOrERoot] at hno⟩
  termination_by (P.complexity, 1, sizeOf body)
  decreasing_by
    all_goals first
      | (simp_wf; right; right; first
          | omega
          | exact sizeOf_impE_left _ _
          | exact sizeOf_impE_right _ _
          | (rw [sizeOf_cast]; omega))
      | (simp_wf; exact lex3_of_le_of_lt hle (by omega))

end

/-- L6: structural normalization driver. Recursively normalize an arbitrary derivation into a
strongly-normal derivation of the same conclusion: dispatch the elimination cases to the smart
eliminators `snAndE1Form`/`snAndE2Form`/`snImpEForm`/`snOrEForm` (which renormalize any redex they
expose) and reassemble the introduction/leaf cases from the normalized children. -/
private def Theory.Derivation.snForm {G : Ctx Atom} {A : Proposition Atom} :
    (d : T.Derivation G A) → {d' : T.Derivation G A // d'.isStronglyNormal = true}
  | ax h => ⟨ax h, rfl⟩
  | ass h => ⟨ass h, rfl⟩
  | andI _ D₁ D₂ =>
      let s₁ := snForm D₁
      let s₂ := snForm D₂
      ⟨andI _ s₁.1 s₂.1, by simp only [isStronglyNormal, Bool.and_eq_true]; exact ⟨s₁.2, s₂.2⟩⟩
  | andE1 _ D =>
      let e := snForm D
      snAndE1Form e.1 e.2
  | andE2 _ D =>
      let e := snForm D
      snAndE2Form e.1 e.2
  | orI1 _ D =>
      let s := snForm D
      ⟨orI1 _ s.1, by simpa only [isStronglyNormal] using s.2⟩
  | orI2 _ D =>
      let s := snForm D
      ⟨orI2 _ s.1, by simpa only [isStronglyNormal] using s.2⟩
  | orE _ D DA DB =>
      let sd := snForm D
      let sA := snForm DA
      let sB := snForm DB
      snOrEForm sd.1 sd.2 sA.1 sA.2 sB.1 sB.2
  | impI _ D =>
      let s := snForm D
      ⟨impI _ s.1, by simpa only [isStronglyNormal] using s.2⟩
  | impE D E =>
      let sf := snForm D
      let sa := snForm E
      snImpEForm sf.1 sf.2 sa.1 sa.2

/-- Every derivation has a strongly-normal form of the same conclusion: the existential
witness extracted from the structural driver `snForm`. -/
private theorem Theory.Derivation.exists_stronglyNormal_form {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) : ∃ d' : T.Derivation G A, d'.isStronglyNormal = true :=
  ⟨(snForm d).1, (snForm d).2⟩

end Cslib.Logic.PL
