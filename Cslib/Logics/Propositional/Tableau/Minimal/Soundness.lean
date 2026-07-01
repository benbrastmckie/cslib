/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness

/-! # Minimal Tableau Soundness

This module proves soundness of the minimal propositional tableau: if the tableau
closes on `φ` (starting from `F(φ)` at world 0), then `φ` is minimally valid.

## Main Results

- `minClosed_unsatisfiable`: A minimally closed branch is unsatisfiable in any Kripke model.
- `minimalTableau_sound`: If `minimalTableau φ = closed`, then `MValid φ`.

## Strategy

Soundness proceeds by contrapositive, reusing the intuitionistic infrastructure:

1. `minClosed_unsatisfiable` uses `Branch.hasContradiction`: a minimally closed branch
   contains T(φ) and F(φ) at the same world, which contradicts `IForces val bf w φ`
   and `¬ IForces val bf w φ` for any `botForces`. This is simpler than the intuitionistic
   case (which required `botForces = fun _ => False` specifically).

2. `minimalTableau_sound` instantiates `intExpandBranches_closed_unsat` with
   `isMinimallyClosed` and `minClosed_unsatisfiable`, mirroring `intuitionisticTableau_sound`.

## Design

Branch satisfiability for minimal logic reuses `intBranchSatisfied` from
`Intuitionistic.Soundness` directly -- both use
`∀ sf ∈ b, (sf.sign = .pos → IForces ... sf.formula) ∧ (sf.sign = .neg → ¬ IForces ...)`.
The difference lies only in how `botForces` is instantiated at use sites.

## Notes on sorry

This module is sorry-free. `intExpandBranches_closed_unsat` is proved in
`Intuitionistic.Soundness`, and `minimalTableau_sound` inherits no outstanding obligations.
Both Minimal and Intuitionistic Tableau soundness are fully proved.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Closure Unsatisfiability -/

omit [Hashable Atom] in
/-- A minimally closed branch is unsatisfiable in any Kripke model.

`isMinimallyClosed b = true` means `Branch.hasContradiction b = true`, i.e., there
exist T(φ) and F(φ) at the same world label for some formula φ. The branch satisfier
then provides both `IForces val botForces w φ` and `¬ IForces val botForces w φ`,
a contradiction regardless of the choice of `botForces`. -/
lemma minClosed_unsatisfiable {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (hclosed : isMinimallyClosed b = true) :
    ¬ intBranchSatisfied val botForces worldOf b := by
  intro hsat
  -- isMinimallyClosed = Branch.hasContradiction = findContradiction.isSome
  simp only [isMinimallyClosed, Branch.hasContradiction, Branch.findContradiction] at hclosed
  -- Extract witness sf_pos from findSome?
  rw [List.findSome?_isSome_iff] at hclosed
  obtain ⟨sf_pos, hsf_pos_mem, hcond⟩ := hclosed
  -- hcond : (if sf_pos.isPos then if b.any ... then some (...) else none else none).isSome
  split_ifs at hcond with hispos hneg
  · -- sf_pos is positive and there is a negative match: derive contradiction
    -- hneg : (b.any fun sf' => sf'.sign == .neg && ...) = true
    rw [List.any_eq_true] at hneg
    obtain ⟨sf_neg, hsf_neg_mem, hneg_cond⟩ := hneg
    simp only [Bool.and_eq_true] at hneg_cond
    obtain ⟨⟨hneg_sign_b, hneg_form_b⟩, hneg_label_b⟩ := hneg_cond
    -- Convert BEq results to =
    simp only [beq_iff_eq] at hneg_sign_b hneg_label_b
    have hneg_form_eq : sf_neg.formula = sf_pos.formula :=
      eq_of_beq hneg_form_b
    -- sf_pos.sign = .pos from isPos
    simp only [SignedFormula.isPos, Sign.isPos] at hispos
    have hpos_sign : sf_pos.sign = .pos := by
      rcases sf_pos with ⟨sign, _, _⟩; cases sign <;> simp_all
    -- Get satisfaction info from the branch satisfier
    have hsat_pos := hsat sf_pos hsf_pos_mem
    have hsat_neg := hsat sf_neg hsf_neg_mem
    rw [hpos_sign] at hsat_pos
    rw [hneg_sign_b, hneg_label_b, hneg_form_eq] at hsat_neg
    exact hsat_neg.2 rfl (hsat_pos.1 rfl)
  · simp at hcond
  · simp at hcond

/-! ## Main Soundness Theorem -/

omit [Hashable Atom] in
/-- **Minimal Tableau Soundness**: If `minimalTableau φ = closed`, then `MValid φ`.

The proof instantiates `intExpandBranches_closed_unsat` with `isMinimallyClosed` and
`minClosed_unsatisfiable`, mirroring `intuitionisticTableau_sound` exactly. The key
differences from the intuitionistic case:
- `botForces` is arbitrary (from the MValid quantifier).
- `isMinimallyClosed` (all complementary pairs) is used instead of `isIntuitionisticallyClosed`.

This theorem is sorry-free; `intExpandBranches_closed_unsat` is now fully proved. -/
theorem minimalTableau_sound (φ : Proposition Atom)
    (h : minimalTableau φ = .closed) : MValid φ := by
  intro World _ val botForces v_uc bf_uc w₀
  by_contra hneg
  let worldOf : Nat → World := fun _ => w₀
  have hsat : intBranchSatisfied val botForces worldOf [⟨.neg, φ, 0⟩] := by
    intro sf hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    subst hmem
    exact ⟨fun h' => absurd h' (Sign.noConfusion), fun _ => hneg⟩
  simp only [minimalTableau] at h
  apply intExpandBranches_closed_unsat val botForces v_uc bf_uc _
    isMinimallyClosed
    (fun worldOf' b hcl => minClosed_unsatisfiable val botForces worldOf' b hcl)
    [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] (by rfl) (by rfl) (by rfl)
      (by
        intro b edges nw hmem
        simp only [List.zip_cons_cons, List.zip_nil_right, List.zip_nil_left,
          List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        obtain ⟨⟨hb, he⟩, hnw⟩ := hmem
        subst hb; subst he; subst hnw
        refine ⟨?_, ?_⟩
        · intro sf hsf
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf
          simp [hsf]
        · intro c p hcp
          simp only [List.not_mem_nil] at hcp) h
    [⟨.neg, φ, 0⟩] []
  · simp [List.zip_cons_cons, List.zip_nil_right]
  · exact fun w w' hacc => by
      simp only [isAccessible] at hacc
      split_ifs at hacc with heq
      · have hw : w = w' := by exact_mod_cast beq_iff_eq.mp heq
        exact le_of_eq (congrArg worldOf hw)
      · simp [isAccessible.go] at hacc
  · exact hsat

/-! ## Countermodel Bot Predicate and No-Contradiction

These definitions are placed here (rather than in `Min/Completeness.lean`) so that
`Intuitionistic/Scheme.lean` can import them without creating a circular dependency with
the Completeness modules. -/

/-- The `botForces` predicate for the minimal countermodel.

`minBranchBotForces b w = true` iff T(⊥) appears at label `w` on the branch `b`.

This is upward-closed by the persistence fixpoint: if T(⊥) is at world w and w ≤ w',
then T(⊥) is also at w' (since T(⊥) is a T-formula and persistence propagates all
T-formulas from accessible worlds). -/
def minBranchBotForces (b : IBranch Atom) (w : Nat) : Prop :=
  b.any (fun sf =>
    sf.sign == .pos && sf.formula == (HasBot.bot : Proposition Atom) && sf.label == w)

omit [Hashable Atom] in
/-- An open minimal branch has no complementary T(φ)/F(φ) pair at the same label.

This follows directly from `isMinimallyClosed b = false`: if T(φ) and F(φ) were both
at label l, then `Branch.hasContradiction b = true`, which means `isMinimallyClosed b = true`,
contradicting openness. -/
lemma minOpen_no_contradiction (b : IBranch Atom)
    (hopen : isMinimallyClosed b = false) (φ : Proposition Atom) (w : Nat) :
    ¬ (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) ∧
       b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w)) := by
  intro ⟨hpos, hneg⟩
  -- The branch has T(φ) at w and F(φ) at w: show hasContradiction = true, contradicting hopen
  have hcontra : isMinimallyClosed b = true := by
    simp only [isMinimallyClosed, Branch.hasContradiction]
    rw [List.any_eq_true] at hpos hneg
    obtain ⟨sf_pos, hsf_pos_mem, hpos_cond⟩ := hpos
    obtain ⟨sf_neg, hsf_neg_mem, hneg_cond⟩ := hneg
    simp only [Bool.and_eq_true] at hpos_cond hneg_cond
    obtain ⟨⟨hpos_sign_b, hpos_form_b⟩, hpos_label_b⟩ := hpos_cond
    obtain ⟨⟨hneg_sign_b, hneg_form_b⟩, hneg_label_b⟩ := hneg_cond
    simp only [beq_iff_eq] at hpos_sign_b hneg_sign_b hpos_label_b hneg_label_b
    -- Convert formula BEq to propositional equality
    have hpos_form_eq : sf_pos.formula = φ :=
      eq_of_beq hpos_form_b
    have hneg_form_eq : sf_neg.formula = φ :=
      eq_of_beq hneg_form_b
    -- Show findContradiction.isSome via cases on the findSome? result
    simp only [Branch.findContradiction, Option.isSome]
    cases hfind : List.findSome? (fun sf =>
        if sf.isPos = true then
          if (List.any b fun sf' =>
              sf'.sign == Sign.neg && sf'.formula == sf.formula && sf'.label == sf.label) = true
          then some (sf.formula, sf.label)
          else none
        else none) b with
    | some _ => rfl
    | none =>
      exfalso
      simp only [List.findSome?_eq_none_iff] at hfind
      have h_none := hfind sf_pos hsf_pos_mem
      simp only [SignedFormula.isPos, hpos_sign_b, Sign.isPos, ite_true,
                 List.any_eq_true] at h_none
      simp only [ite_eq_right_iff] at h_none
      -- h_none : (∃ x ∈ b with x.sign = .neg && formula=sf_pos.formula && label=sf_pos.label)
      --          → some (...) = none
      -- We have sf_neg as such a witness
      have hwitness := h_none ⟨sf_neg, hsf_neg_mem, by
        simp only [Bool.and_eq_true, BEq.beq]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · -- (sf_neg.sign == .neg) = true
          exact hneg_sign_b ▸ beq_self_eq_true _
        · -- (sf_neg.formula == sf_pos.formula) = true
          -- We know sf_neg.formula = φ = sf_pos.formula
          rw [hpos_form_eq]; exact hneg_form_b
        · -- (sf_neg.label == sf_pos.label) = true
          simp only [decide_eq_true_eq]; exact hneg_label_b.trans hpos_label_b.symm⟩
      exact absurd hwitness (by simp)
  simp [hcontra] at hopen

end Cslib.Logic.PL

end
