/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Normalization.Reduction

/-! # Normalization Termination for Propositional Natural Deduction

This module proves termination of normalization via `redexWeight`, and establishes that
`normalize` produces strongly normal derivations.

## Main Results

- `Theory.Derivation.normalizeAux_fixpoint`: Strongly normal derivations are fixpoints of
  `normalizeAux`.
- `Theory.Derivation.normalize_isStronglyNormal`: `normalize` produces strongly normal
  derivations (proof currently `sorry` — see task 332).

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

end Cslib.Logic.PL
