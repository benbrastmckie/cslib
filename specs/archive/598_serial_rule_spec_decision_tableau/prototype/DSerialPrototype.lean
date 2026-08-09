/-
Prototype (research artifact, not library code): serial-successor rule spec measurement.

Built with `lake env lean` at HEAD ad19c80d. Zero `sorry`, zero new axioms
(`#print axioms` reports only propext / Classical.choice / Quot.sound).

Contents:
  * `modalApplyOneD` -- Route E's D rule: two PERSISTENT dual arms
    (T(box psi)@w |- T(dia psi)@w, F(dia psi)@w |- F(box psi)@w), structurally a clone of
    `modalApplyOneT` with the T self-propagation helpers swapped for the D duals.
  * Machine-checked discharges of RuleApplicationSpec F1, F8, F9, F10, F11', F12'
    for `modalApplyOneD` -- in particular F9 `boxPosNotExpanding`, the field the
    eight-corner research reported as unsatisfiable for D.
  * `modalApplyOneD_outputsSubsetUniverse_fails` -- a machine-checked proof that F2
    (`outputsSubsetUniverse`) is the field that actually fails, and that it fails for a
    universe reason (the emitted dual escapes `modalSubfmls`), not a rule-shape reason.
  * `modalSubfmlsDual` + `modalSubfmlsDual_length_le` -- the dual-closed subformula list
    obeys the SAME `2 * modalComplexity phi + 1` bound as `modalSubfmls`, so no measure
    constant (`modalWorldBound`, `modalFuel`, `modalUniverse_length_le`) needs to change.
-/

module

public import Cslib.Logics.Modal.Tableau.GenericDriver
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.Support.Accessibility

/-! Prototype part 2: remaining cheap fields + the F2 counterexample. -/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

def modalDBoxDual (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, .diamond φ, w⟩
  if b.any (· == sf) then [] else [sf]

def modalDDiaNegDual (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, .box φ, w⟩
  if b.any (· == sf) then [] else [sf]

def modalApplyOneD
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (kResult, kAcc) := modalApplyOne sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let dualNew := modalDBoxDual b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ dualNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if dualNew.isEmpty then (.notApplicable, kAcc) else (.persistent dualNew, kAcc)
    | other => (other, kAcc)
  | .neg, .diamond φ =>
    let dualNew := modalDDiaNegDual b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ dualNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if dualNew.isEmpty then (.notApplicable, kAcc) else (.persistent dualNew, kAcc)
    | other => (other, kAcc)
  | _, _ => (kResult, kAcc)

omit [Hashable Atom] in
lemma modalApplyOneD_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneD sf b acc = modalApplyOne sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneD
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

omit [Hashable Atom] in
/-- Local re-derivation of TDriver's private `modalApplyOne_boxPos_acc_eq`. -/
lemma kBoxPos_acc_eq (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = acc := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  split_ifs <;> rfl

omit [Hashable Atom] in
lemma kDiaNeg_acc_eq (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
      b acc).snd = acc := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
      = false := by
    rw [tryAllPropRules_neg]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  split_ifs <;> rfl

omit [Hashable Atom] in
lemma modalApplyOneD_boxPos_snd (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOne (⟨.pos, .box φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneD]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
lemma modalApplyOneD_diaNeg_snd (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).snd := by
  simp only [modalApplyOneD]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [DecidableEq Atom] [Hashable Atom] in
private lemma not_shape_of_not_or' {sf : SignedFormula (Proposition Atom) WorldIndex}
    (hshape : ¬ ((sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ))) :
    ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
  ⟨fun h => hshape (Or.inl h), fun h => hshape (Or.inr h)⟩

omit [Hashable Atom] in
/-- **F1 freshLocal**. -/
lemma modalApplyOneD_freshLocal
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneD sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneD sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
      (modalApplyOneD sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  by_cases hshape : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hshape with ⟨hsign, φ, hform⟩ | ⟨hsign, φ, hform⟩
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl (modalApplyOneD_boxPos_snd b acc φ w ▸ kBoxPos_acc_eq b acc φ w)
    · obtain ⟨s, form, w⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact Or.inl (modalApplyOneD_diaNeg_snd b acc φ w ▸ kDiaNeg_acc_eq b acc φ w)
  · rw [modalApplyOneD_eq_of_not_boxPos_diaNeg sf b acc (not_shape_of_not_or' hshape)]
    exact modalApplyOne_fresh_local sf b acc

omit [Hashable Atom] in
/-- **F8 localShapeInvariance**. -/
lemma modalApplyOneD_localShapeInvariance
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) :
    (modalApplyOneD ⟨s, φ, w⟩ b acc).1 = (modalApplyOneD ⟨s, φ, w⟩ b' acc').1 := by
  have hnotshape : ∀ (b'' : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc'' : Accessibility),
      modalApplyOneD (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc''
        = modalApplyOne (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b'' acc'' := by
    intro b'' acc''
    apply modalApplyOneD_eq_of_not_boxPos_diaNeg
    exact ⟨by rintro ⟨-, ψ, hform⟩; exact hnb ψ hform,
           by rintro ⟨-, ψ, hform⟩; exact hnd ψ hform⟩
  rw [hnotshape b acc, hnotshape b' acc']
  exact modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'

omit [Hashable Atom] in
/-- **F11' boxNegWitness'**. -/
lemma modalApplyOneD_boxNegWitness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneD (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  rw [modalApplyOneD_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩]
  exact modalApplyOne_boxNeg_witness b acc ψ w

omit [Hashable Atom] in
/-- **F12' diaPosWitness'**. -/
lemma modalApplyOneD_diaPosWitness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneD (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneD (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  rw [modalApplyOneD_eq_of_not_boxPos_diaNeg _ b acc ⟨by simp, by simp⟩]
  exact modalApplyOne_diamondPos_witness b acc ψ w

/-! ### The rank-step content check: the D dual is depth-preserving, not depth-decreasing. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- The only arithmetic difference from T's `rankStep`: T emits a strictly shallower formula,
D emits an equally-deep one. Both satisfy the `≤` the field requires. -/
lemma modalDepth_diamond_eq_box (ψ : Proposition Atom) :
    modalDepth (Proposition.diamond ψ) = modalDepth (Proposition.box ψ) := rfl

/-! ### F2 `outputsSubsetUniverse` provably FAILS for `modalApplyOneD`. -/

/-- The concrete counterexample: at `φ0 = □p`, branch `b = [T(□p)@0]`, empty `acc`, the D rule
emits `T(◇p)@0`, which is not in `modalUniverse (□p)` because `◇p ∉ modalSubfmls (□p)`.
All four hypotheses of the field are discharged. -/
theorem modalApplyOneD_outputsSubsetUniverse_fails :
    ¬ (∀ (φ0 : Proposition Nat)
        (sf : SignedFormula (Proposition Nat) WorldIndex)
        (b : List (SignedFormula (Proposition Nat) WorldIndex)) (acc : Accessibility),
      (∀ x ∈ b, x ∈ modalUniverse φ0) → sf ∈ b → accFreshInv b acc →
      modalMaxWorld b < modalWorldBound φ0 →
      (match (modalApplyOneD sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
        | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverse φ0
        | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
        | .notApplicable => True)) := by
  intro h
  set p : Proposition Nat := .atom 0 with hp
  set φ0 : Proposition Nat := .box p with hφ0
  set sf : SignedFormula (Proposition Nat) WorldIndex := ⟨.pos, .box p, 0⟩ with hsf
  have hb : ∀ x ∈ [sf], x ∈ modalUniverse φ0 := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp only [modalUniverse, List.mem_flatMap, List.mem_range, hsf, hφ0, modalSubfmls]
    exact ⟨0, by simp [modalWorldBound], .box p, by simp, by simp⟩
  have hmax : modalMaxWorld [sf] < modalWorldBound φ0 := by
    simp only [hsf, hφ0, hp, modalMaxWorld, modalWorldBound, modalComplexity, List.foldl]
    decide
  have hres := h φ0 sf [sf] Accessibility.empty hb (by simp) (accFreshInv_empty _) hmax
  -- Compute the D result: K's boxPos is notApplicable (no successors), dual is nonempty.
  have hfst : (modalApplyOneD sf [sf] Accessibility.empty).fst
      = .persistent [(⟨.pos, .diamond p, 0⟩ : SignedFormula (Proposition Nat) WorldIndex)] := by
    have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
        = false := by
      rw [hsf, tryAllPropRules_pos]
      simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
    simp only [modalApplyOneD, modalApplyOne, hsf]
    rw [if_neg (by simp [hsf] at htry ⊢; exact htry)]
    simp [boxPropagation, Accessibility.successorsOf, Accessibility.empty, modalDBoxDual]
  rw [hfst] at hres
  have hmem := hres (⟨.pos, .diamond p, 0⟩ : SignedFormula (Proposition Nat) WorldIndex)
    (List.mem_singleton.mpr rfl)
  have hform := modalUniverse_mem_formula hmem
  simp [hφ0, hp, modalSubfmls] at hform

/-! ### Dual-closed subformula list (Route E's universe fix). -/

/-- Dual-closed subformula list: every `□ψ` drags in `◇ψ` and vice versa. -/
def modalSubfmlsDual : Proposition Atom → List (Proposition Atom)
  | .atom p  => [.atom p]
  | .bot     => [.bot]
  | .imp a b => .imp a b :: modalSubfmlsDual a ++ modalSubfmlsDual b
  | .and a b => .and a b :: modalSubfmlsDual a ++ modalSubfmlsDual b
  | .or a b  => .or a b :: modalSubfmlsDual a ++ modalSubfmlsDual b
  | .box a   => .box a :: .diamond a :: modalSubfmlsDual a
  | .diamond a => .diamond a :: .box a :: modalSubfmlsDual a

omit [DecidableEq Atom] [Hashable Atom] in
/-- **The decisive measurement**: the dual-closed list obeys the SAME length bound
`2 * modalComplexity φ + 1` as `modalSubfmls`. Hence `modalWorldBound`, `modalUniverse_length_le`,
and `modalFuel` need no constant change. -/
lemma modalSubfmlsDual_length_le (φ : Proposition Atom) :
    (modalSubfmlsDual φ).length ≤ 2 * modalComplexity φ + 1 := by
  induction φ with
  | atom p => simp [modalSubfmlsDual]
  | bot => simp [modalSubfmlsDual]
  | imp a b iha ihb =>
    simp only [modalSubfmlsDual, List.length_cons, List.length_append, modalComplexity_imp]
    omega
  | and a b iha ihb =>
    simp only [modalSubfmlsDual, List.length_cons, List.length_append, modalComplexity_and]
    omega
  | or a b iha ihb =>
    simp only [modalSubfmlsDual, List.length_cons, List.length_append, modalComplexity_or]
    omega
  | box a iha =>
    simp only [modalSubfmlsDual, List.length_cons, modalComplexity_box]
    omega
  | diamond a iha =>
    simp only [modalSubfmlsDual, List.length_cons, modalComplexity_diamond]
    omega

omit [DecidableEq Atom] [Hashable Atom] in
/-- The dual-closed list contains everything `modalSubfmls` does. -/
lemma modalSubfmls_subset_dual (φ : Proposition Atom) :
    ∀ ψ ∈ modalSubfmls φ, ψ ∈ modalSubfmlsDual φ := by
  induction φ <;> intro ψ hψ <;>
    simp only [modalSubfmls, modalSubfmlsDual, List.mem_cons, List.mem_append] at hψ ⊢ <;>
    tauto

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Dual closure**: `□ψ ∈ modalSubfmlsDual φ → ◇ψ ∈ modalSubfmlsDual φ`. Exactly what D's
box-positive arm needs to keep `outputsSubsetUniverse` (F2). -/
lemma modalSubfmlsDual_box_dual (φ : Proposition Atom) :
    ∀ ψ, (Proposition.box ψ) ∈ modalSubfmlsDual φ →
      (Proposition.diamond ψ) ∈ modalSubfmlsDual φ := by
  induction φ <;> intro ψ hψ <;>
    simp only [modalSubfmlsDual, List.mem_cons, List.mem_append, Proposition.box.injEq,
      Proposition.diamond.injEq, reduceCtorEq, false_or, or_false] at hψ ⊢ <;>
    tauto

omit [DecidableEq Atom] [Hashable Atom] in
/-- Dual of `modalSubfmlsDual_box_dual`, needed by D's diamond-negative arm. -/
lemma modalSubfmlsDual_dia_dual (φ : Proposition Atom) :
    ∀ ψ, (Proposition.diamond ψ) ∈ modalSubfmlsDual φ →
      (Proposition.box ψ) ∈ modalSubfmlsDual φ := by
  induction φ <;> intro ψ hψ <;>
    simp only [modalSubfmlsDual, List.mem_cons, List.mem_append, Proposition.box.injEq,
      Proposition.diamond.injEq, reduceCtorEq, false_or, or_false] at hψ ⊢ <;>
    tauto


end Cslib.Logic.Modal.Tableau

end

section Audit
open Cslib.Logic.Modal.Tableau
#print axioms Cslib.Logic.Modal.Tableau.modalApplyOneD_freshLocal
#print axioms Cslib.Logic.Modal.Tableau.modalApplyOneD_localShapeInvariance
#print axioms Cslib.Logic.Modal.Tableau.modalApplyOneD_boxNegWitness
#print axioms Cslib.Logic.Modal.Tableau.modalApplyOneD_diaPosWitness
#print axioms Cslib.Logic.Modal.Tableau.modalApplyOneD_outputsSubsetUniverse_fails
end Audit
