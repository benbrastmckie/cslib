/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Tactic.Ring
import Cslib.Logics.Modal.Tableau.Completeness
public import Cslib.Logics.Modal.Tableau.Saturation
public import Cslib.Logics.Modal.Tableau.LoopInduction

/-! # Modal K Tableau Finite-Model-Property Termination Measure

This module defines the finite world-bounded signed-formula universe `modalUniverse φ`
and the base-3 counting termination measure `modalExpMeasure` used to prove that the
(exponential) `modalFuel` bound in `Saturation.lean` is sufficient for the modal K
tableau saturation loop to reach a Hintikka set before fuel is exhausted.

## Main Definitions

- `modalSubfmls`: Structural subformula list of a `Proposition Atom`.
- `modalDepth`: Modal (box-nesting) depth of a `Proposition Atom`.
- `modalWorldBound`: A-priori bound on the number of worlds a saturating tableau on `φ`
  can create.
- `modalUniverse`: The fixed finite signed-formula universe `U(φ)` (both signs, all
  subformulas, all world labels `0..W`).
- `modalWork`: The per-branch counting measure `R(b,e) = |U\b| + |U\e|`.
- `modalExpMeasure`: The base-3 damped worklist measure `Σ 3^(modalWork U bᵢ eᵢ)`.

## Main Results

- `modalSubfmls_length_le`, `modalDepth_le_complexity`, `modalUniverse_length_le`: size
  bounds on the universe.
- `modalExpMeasure_entry_le_fuel`: the worklist measure at the tableau entry point is
  `≤ modalFuel φ`, connecting the counting measure to the closed-form fuel bound defined
  in `Saturation.lean`.

## Design

The measure `R` is a *counting* measure over a fixed finite universe, not a complexity
measure: the persistent modal rules (`boxPos`, `diamondNeg`) re-fire without shrinking
branch complexity, so a `3^complexity` exponent is non-decreasing on those rules. Counting
against a fixed finite `U(φ)` restores strict decrease on every rule kind, because each
step either adds a new formula to `b` or to `e` (both subsets of the finite `U`).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Subformula List and Depth -/

/-- Structural subformula list of a `Proposition Atom` (Lukasiewicz `imp`/`box`
recursion). Every node of `φ`'s syntax tree contributes exactly one entry. -/
def modalSubfmls : Proposition Atom → List (Proposition Atom)
  | .atom p  => [.atom p]
  | .bot     => [.bot]
  | .imp a b => .imp a b :: modalSubfmls a ++ modalSubfmls b
  | .box a   => .box a :: modalSubfmls a

/-- The subformula list has length at most `2 * modalComplexity φ + 1`. -/
lemma modalSubfmls_length_le (φ : Proposition Atom) :
    (modalSubfmls φ).length ≤ 2 * modalComplexity φ + 1 := by
  induction φ with
  | atom p => simp [modalSubfmls]
  | bot => simp [modalSubfmls]
  | imp a b iha ihb =>
    simp only [modalSubfmls, List.length_cons, List.length_append, modalComplexity_imp]
    omega
  | box a iha =>
    simp only [modalSubfmls, List.length_cons, modalComplexity_box]
    omega

/-- Modal (box-nesting) depth of a `Proposition Atom`: `box` adds one, `imp` takes the
max of its two sub-depths. -/
def modalDepth : Proposition Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp a b => max (modalDepth a) (modalDepth b)
  | .box a => 1 + modalDepth a

/-- Modal depth is bounded by structural complexity. -/
lemma modalDepth_le_complexity (φ : Proposition Atom) :
    modalDepth φ ≤ modalComplexity φ := by
  induction φ with
  | atom p => simp [modalDepth]
  | bot => simp [modalDepth]
  | imp a b iha ihb =>
    simp only [modalDepth, modalComplexity_imp]
    omega
  | box a iha =>
    simp only [modalDepth, modalComplexity_box]
    omega

/-! ## World Bound and Universe -/

/-- A-priori bound on the number of distinct worlds a saturating tableau on `φ` can
create: `Sf(φ)^(complexity φ + 1)`, where `Sf(φ) := 2 * modalComplexity φ + 1` bounds
the branching factor and `complexity φ + 1 ≥ modalDepth φ + 1` bounds the forest depth
(`modalDepth_le_complexity`). -/
def modalWorldBound (φ : Proposition Atom) : Nat :=
  (2 * modalComplexity φ + 1) ^ (modalComplexity φ + 1)

/-- The fixed finite signed-formula universe `U(φ)`: both signs, every subformula of
`φ`, at every world label `0 .. modalWorldBound φ`. -/
def modalUniverse (φ : Proposition Atom) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (List.range (modalWorldBound φ + 1)).flatMap (fun w =>
    (modalSubfmls φ).flatMap (fun ψ => [⟨.pos, ψ, w⟩, ⟨.neg, ψ, w⟩]))

/-- Helper: if every image element of `f` on `l` is bounded by `c`, the summed image is
bounded by `l.length * c`. Self-contained (avoids hunting for the exact Mathlib name). -/
private lemma sum_map_le_length_mul {α : Type*} (l : List α) (f : α → Nat) (c : Nat)
    (h : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : f x ≤ c := h x (by simp)
    have hxs : (xs.map f).sum ≤ xs.length * c := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have heq : (xs.length + 1) * c = xs.length * c + c := by ring
    omega

/-- The universe has length at most `2 * (2 * modalComplexity φ + 1) * (modalWorldBound φ + 1)`. -/
lemma modalUniverse_length_le (φ : Proposition Atom) :
    (modalUniverse φ).length ≤
      2 * (2 * modalComplexity φ + 1) * (modalWorldBound φ + 1) := by
  have hinner : ∀ w : WorldIndex,
      ((modalSubfmls φ).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                    ⟨.neg, ψ, w⟩])).length
        ≤ 2 * (2 * modalComplexity φ + 1) := by
    intro w
    rw [List.length_flatMap]
    have hb : (List.map (fun ψ =>
        ([(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex), ⟨.neg, ψ, w⟩]).length)
        (modalSubfmls φ)).sum ≤ (modalSubfmls φ).length * 2 :=
      sum_map_le_length_mul (modalSubfmls φ) _ 2 (fun ψ _ => by simp)
    have hlen := modalSubfmls_length_le φ
    omega
  unfold modalUniverse
  rw [List.length_flatMap]
  have houter : (List.map (fun w =>
      ((modalSubfmls φ).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                    ⟨.neg, ψ, w⟩])).length) (List.range (modalWorldBound φ + 1))).sum
      ≤ (List.range (modalWorldBound φ + 1)).length * (2 * (2 * modalComplexity φ + 1)) :=
    sum_map_le_length_mul (List.range (modalWorldBound φ + 1)) _
      (2 * (2 * modalComplexity φ + 1)) (fun w _ => hinner w)
  rw [List.length_range] at houter
  calc (List.map (fun w =>
        ((modalSubfmls φ).flatMap
          (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                      ⟨.neg, ψ, w⟩])).length) (List.range (modalWorldBound φ + 1))).sum
      ≤ (modalWorldBound φ + 1) * (2 * (2 * modalComplexity φ + 1)) := houter
    _ = 2 * (2 * modalComplexity φ + 1) * (modalWorldBound φ + 1) := by ring

/-! ## The Counting Measure -/

/-- The per-branch counting measure `R(b, e) := |U \ b| + |U \ e|`: the number of
universe elements not yet on the branch, plus the number not yet expanded. -/
def modalWork (U b e : List (SignedFormula (Proposition Atom) WorldIndex)) : Nat :=
  U.countP (fun sf => !(b.any (· == sf))) + U.countP (fun sf => !(e.any (· == sf)))

/-- The base-3 damped worklist measure: `Σ 3^(modalWork U bᵢ eᵢ)` over the zipped
branch/expanded-set worklist. -/
def modalExpMeasure (U : List (SignedFormula (Proposition Atom) WorldIndex))
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex))) :
    Nat :=
  ((branches.zip expandedSets).map (fun p => 3 ^ modalWork U p.1 p.2)).sum

/-! ## Entry-Point Bridge -/

/-- At the tableau entry point, the worklist measure over the universe `U(φ)` is
bounded by `modalFuel φ`. This connects the counting measure defined here to the
closed-form fuel bound in `Saturation.lean`, which is stated purely over
`modalComplexity` to avoid an import cycle (`FmpMeasure` imports `Saturation`). -/
lemma modalExpMeasure_entry_le_fuel (φ : Proposition Atom) :
    modalExpMeasure (modalUniverse φ) [[(⟨.neg, φ, 0⟩ :
      SignedFormula (Proposition Atom) WorldIndex)]] [[]] ≤ modalFuel φ := by
  have hmeas : modalExpMeasure (modalUniverse φ)
      [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      = 3 ^ modalWork (modalUniverse φ)
          [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] := by
    simp [modalExpMeasure]
  rw [hmeas]
  have hwork : modalWork (modalUniverse φ)
      [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 2 * (modalUniverse φ).length := by
    unfold modalWork
    have h1 : (modalUniverse φ).countP
        (fun sf => !(([(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]).any
          (· == sf))) ≤ (modalUniverse φ).length :=
      List.countP_le_length
    have h2 : (modalUniverse φ).countP
        (fun sf => !((([] : List (SignedFormula (Proposition Atom) WorldIndex))).any
          (· == sf))) = (modalUniverse φ).length := by
      simp
    omega
  have hUlen := modalUniverse_length_le φ
  have hexp : 2 * (modalUniverse φ).length ≤
      4 * (2 * modalComplexity φ + 1) * ((2 * modalComplexity φ + 1) ^
        (modalComplexity φ + 1) + 1) := by
    have h2U : 2 * (modalUniverse φ).length ≤
        2 * (2 * (2 * modalComplexity φ + 1) * (modalWorldBound φ + 1)) :=
      Nat.mul_le_mul_left 2 hUlen
    have heq : 2 * (2 * (2 * modalComplexity φ + 1) * (modalWorldBound φ + 1)) =
        4 * (2 * modalComplexity φ + 1) * ((2 * modalComplexity φ + 1) ^
          (modalComplexity φ + 1) + 1) := by
      unfold modalWorldBound; ring
    rw [heq] at h2U
    exact h2U
  have hfinal : modalWork (modalUniverse φ)
      [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] ≤
      4 * (2 * modalComplexity φ + 1) * ((2 * modalComplexity φ + 1) ^
        (modalComplexity φ + 1) + 1) := le_trans hwork hexp
  calc 3 ^ modalWork (modalUniverse φ)
        [(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 3 ^ (4 * (2 * modalComplexity φ + 1) * ((2 * modalComplexity φ + 1) ^
          (modalComplexity φ + 1) + 1)) := Nat.pow_le_pow_right (by norm_num) hfinal
    _ = modalFuel φ := rfl

/-! ## Subformula-Closure: World-Preserving Rules (Phase 1a)

This section proves that formulas emitted by the propositional (α/β) rules, `boxPos`, and
`diamondNeg` — the three rule kinds that do NOT mint a fresh world — are structural
subformulas of the source formula, at a world label that is either unchanged or an existing
successor. This is the closure fact needed for the rule kinds that cannot breach the world
bound, so no world-bound hypothesis is consumed here. The two fresh-world-minting rules
(`diamondPos`, `boxNeg`) and the top-level dispatch lemma are Phase 1b's job. -/

/-- Every `Proposition Atom` is a member of its own structural subformula list (the list
always begins with the formula itself). Marked `@[simp]` so it discharges nested
`modalSubfmls` membership goals as a rewrite. -/
@[simp]
lemma modalSubfmls_self_mem (φ : Proposition Atom) : φ ∈ modalSubfmls φ := by
  cases φ <;> simp [modalSubfmls]

/-- Every formula emitted by a propositional (α/β) rule application via `tryAllPropRules` is a
structural subformula of `sf.formula`, at the unchanged world label `sf.label`. Mirrors the
case-split shape of `classicalApplyOne_output_complexity`
(`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:609`), proving list membership
in place of a complexity sum. -/
lemma modalApplyOne_prop_outputs_subset
    (sf : SignedFormula (Proposition Atom) WorldIndex) :
    (match tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
      | .linear formulas =>
          ∀ x ∈ formulas, x.formula ∈ modalSubfmls sf.formula ∧ x.label = sf.label
      | .branching branches =>
          ∀ x ∈ branches.flatten, x.formula ∈ modalSubfmls sf.formula ∧ x.label = sf.label
      | .persistent formulas =>
          ∀ x ∈ formulas, x.formula ∈ modalSubfmls sf.formula ∧ x.label = sf.label
      | .notApplicable => True) := by
  obtain ⟨s, φ, l⟩ := sf
  rcases s with _ | _
  · rw [tryAllPropRules_pos]
    rcases hA : modalAndOf? φ with _ | ⟨x, y⟩
    · rcases hO : modalOrOf? φ with _ | ⟨x, y⟩
      · rcases hI : modalImpOf? φ with _ | ⟨x, y⟩
        · rcases hN : modalNegOf? φ with _ | x
          · simp
          · obtain rfl := modalNegOf?_eq hN
            intro z hz
            simp only [SignedFormula.formula, SignedFormula.label, List.mem_cons,
              List.not_mem_nil, or_false] at hz ⊢
            subst hz
            simp [modalSubfmls]
        · obtain rfl := modalImpOf?_eq hI
          intro z hz
          simp only [List.mem_flatten,
            List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          obtain ⟨t, ht, hzt⟩ := hz
          rcases ht with rfl | rfl <;> simp_all [modalSubfmls]
      · obtain rfl := modalOrOf?_eq hO
        intro z hz
        simp only [List.mem_flatten,
          List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        obtain ⟨t, ht, hzt⟩ := hz
        rcases ht with rfl | rfl <;> simp_all [modalSubfmls]
    · obtain rfl := modalAndOf?_eq hA
      intro z hz
      simp only [List.mem_cons,
        List.not_mem_nil, or_false] at hz ⊢
      rcases hz with rfl | rfl <;> simp [modalSubfmls]
  · rw [tryAllPropRules_neg]
    rcases hA : modalAndOf? φ with _ | ⟨x, y⟩
    · rcases hO : modalOrOf? φ with _ | ⟨x, y⟩
      · rcases hI : modalImpOf? φ with _ | ⟨x, y⟩
        · rcases hN : modalNegOf? φ with _ | x
          · simp
          · obtain rfl := modalNegOf?_eq hN
            intro z hz
            simp only [List.mem_cons,
              List.not_mem_nil, or_false] at hz ⊢
            subst hz
            simp [modalSubfmls]
        · obtain rfl := modalImpOf?_eq hI
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with rfl | rfl <;> simp [modalSubfmls]
      · obtain rfl := modalOrOf?_eq hO
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        rcases hz with rfl | rfl <;> simp [modalSubfmls]
    · obtain rfl := modalAndOf?_eq hA
      intro z hz
      simp only [List.mem_flatten, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      obtain ⟨t, ht, hzt⟩ := hz
      rcases ht with rfl | rfl <;> simp_all [modalSubfmls]

/-- `boxPos`: `T(□ψ)@w` propagates `T(ψ)@w'` for each recorded successor `w'` of `w`
(`boxPropagation`, `Branch.lean:194-199`). Every emitted formula's formula-component is `ψ`, a
structural subformula of the source `.box ψ`, at a world label that is an existing recorded
successor of `w` (`Rules.lean:83-88`). -/
lemma modalApplyOne_boxPos_outputs_subset
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ boxPropagation b acc ψ w,
      x.formula ∈ modalSubfmls (Proposition.box ψ) ∧ x.label ∈ acc.successorsOf w := by
  intro x hx
  simp only [boxPropagation, List.mem_filterMap] at hx
  obtain ⟨w', hw', hxeq⟩ := hx
  split at hxeq
  · simp at hxeq
  · simp only [Option.some.injEq] at hxeq
    subst hxeq
    exact ⟨by simp [modalSubfmls], hw'⟩

/-- `diamondNeg`: `F(◇φ)@w = F((□(φ→⊥))→⊥)@w` emits `F(φ)@w'` for each recorded successor
`w'` of `w` (`Rules.lean:142-151`). Every emitted formula's formula-component is `φ`, a
structural subformula of the encoded source formula, at a world label that is an existing
recorded successor of `w`. Stated directly over the rule's raw emission expression (rather than
routed through `modalApplyOne`) because `tryAllPropRules`'s `negOf?` pattern also matches the
`.imp (.box _) .bot` shape, so this match arm of `modalApplyOne` is not the reachable path for
that shape — see `modalApplyOne_prop_outputs_subset` for the actually-dispatched pathway. This
lemma records the closure fact for the rule *as written* at `Rules.lean:142-151`. -/
lemma modalApplyOne_diamondNeg_outputs_subset
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ (acc.successorsOf w).filterMap (fun w' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf') then none else some sf'),
      x.formula ∈
        modalSubfmls (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot))
          Proposition.bot) ∧
        x.label ∈ acc.successorsOf w := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨w', hw', hxeq⟩ := hx
  split at hxeq
  · simp at hxeq
  · simp only [Option.some.injEq] at hxeq
    subst hxeq
    exact ⟨by simp [modalSubfmls], hw'⟩

end Cslib.Logic.Modal.Tableau

end
