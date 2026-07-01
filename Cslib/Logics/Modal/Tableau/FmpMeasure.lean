/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Nodup
import Cslib.Logics.Modal.Tableau.Completeness
public import Cslib.Logics.Modal.Tableau.SoundnessStep
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

/-! ## Subformula-Closure: Fresh-World Rules and Top Dispatch (Phase 1b)

This section proves closure for the two fresh-world-minting linear rules (`diamondPos`,
`boxNeg`, `Rules.lean:91-139`), which consume the world-bound hypothesis to show the freshly
minted world label stays inside `U(φ0)`, and assembles the top-level dispatch lemma
`modalApplyOne_outputs_subset` by case analysis over `modalApplyOne`. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Transitivity of `modalSubfmls`: a subformula of a subformula is a subformula. Needed
because the fresh-world rules' propagated groups (`boxProps`, `diaNegProps`) derive their
subformula bound from *other* branch members via the branch invariant, not from the source
formula directly, so a two-step subformula chain must be composed. -/
private lemma modalSubfmls_trans {a b c : Proposition Atom}
    (hab : a ∈ modalSubfmls b) (hbc : b ∈ modalSubfmls c) : a ∈ modalSubfmls c := by
  induction c with
  | atom p =>
    simp only [modalSubfmls, List.mem_singleton] at hbc; subst hbc; exact hab
  | bot =>
    simp only [modalSubfmls, List.mem_singleton] at hbc; subst hbc; exact hab
  | imp x y ihx ihy =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at hbc
    rcases hbc with (rfl | hx) | hy
    · exact hab
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihx hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihy hy))
  | box x ihx =>
    simp only [modalSubfmls, List.mem_cons] at hbc
    rcases hbc with rfl | hx
    · exact hab
    · exact List.mem_cons_of_mem _ (ihx hx)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Constructor direction for `modalUniverse` membership: a signed formula with any sign,
a subformula of `φ0`, at a world label within the bound, is in `U(φ0)`. -/
private lemma mem_modalUniverse_of {φ0 : Proposition Atom} {s : Sign} {φ : Proposition Atom}
    {w : WorldIndex} (hw : w ≤ modalWorldBound φ0) (hφ : φ ∈ modalSubfmls φ0) :
    (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverse φ0 := by
  have hlt : w < modalWorldBound φ0 + 1 := Nat.lt_succ_of_le hw
  simp only [modalUniverse, List.mem_flatMap, List.mem_range]
  exact ⟨w, hlt, φ, hφ, by cases s <;> simp⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Generic form of `mem_modalUniverse_of`, stated for an arbitrary signed formula `z`
rather than a literal anonymous constructor (needed by the top-level dispatch lemma, which
case-splits on `RuleResult`-bound lists of already-opaque signed formulas). -/
private lemma mem_modalUniverse_of' {φ0 : Proposition Atom}
    {z : SignedFormula (Proposition Atom) WorldIndex}
    (hw : z.label ≤ modalWorldBound φ0) (hφ : z.formula ∈ modalSubfmls φ0) :
    z ∈ modalUniverse φ0 := by
  obtain ⟨s, φ, w⟩ := z
  exact mem_modalUniverse_of hw hφ

omit [DecidableEq Atom] [Hashable Atom] in
/-- Extraction: the formula-component of any `modalUniverse φ0` member is a subformula of
`φ0`. -/
private lemma modalUniverse_mem_formula {φ0 : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverse φ0) :
    x.formula ∈ modalSubfmls φ0 := by
  simp only [modalUniverse, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, -, ψ, hψ, heq | heq⟩ := hx <;> (subst heq; exact hψ)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Extraction: the label-component of any `modalUniverse φ0` member is bounded by
`modalWorldBound φ0`. -/
private lemma modalUniverse_mem_label {φ0 : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverse φ0) :
    x.label ≤ modalWorldBound φ0 := by
  simp only [modalUniverse, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, ψ, -, heq | heq⟩ := hx <;> (subst heq; exact Nat.lt_succ_iff.mp hw)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion for `boxPositivesOf`: every `(ψ, src)` pair it returns came from an actual
`T(□ψ)@src` member of the branch (`Branch.lean:180-187`). -/
private lemma mem_boxPositivesOf {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {ψ : Proposition Atom} {src : WorldIndex} (h : (ψ, src) ∈ boxPositivesOf b) :
    (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  simp only [boxPositivesOf, List.mem_filterMap] at h
  obtain ⟨sf, hsfmem, hsfeq⟩ := h
  split at hsfeq
  · rename_i hsign
    split at hsfeq
    · rename_i φ' hform
      simp only [Option.some.injEq, Prod.mk.injEq] at hsfeq
      obtain ⟨rfl, rfl⟩ := hsfeq
      rw [beq_iff_eq] at hsign
      obtain ⟨s, φ, l⟩ := sf
      simp only at hsign hform
      subst hsign; subst hform
      exact hsfmem
    · simp at hsfeq
  · simp at hsfeq

/-- Shared closure fact for the `boxProps` group propagated by both fresh-world rules
(`diamondPos`, `Rules.lean:97-102`; `boxNeg`, `Rules.lean:123-128`): each propagated
`T(ψ)@w'` comes from a `T(□ψ)@w ∈ b`, hence `ψ` is a subformula of `φ0`. Factored out since
the `boxProps` construction is byte-identical between the two rules. -/
private lemma boxProps_outputs_subset (φ0 : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hwbound : modalNextWorld b ≤ modalWorldBound φ0) :
    ∀ x ∈ (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex :=
            ⟨.pos, ψ, modalNextWorld b⟩
          if b.any (· == sf') then none else some sf'
        else none),
    x ∈ modalUniverse φ0 := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨⟨ψ, src⟩, hψsrc, heq⟩ := hx
  split at heq
  · split at heq
    · simp at heq
    · simp only [Option.some.injEq] at heq
      subst heq
      have hψbox : (⟨.pos, .box ψ, src⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := mem_boxPositivesOf hψsrc
      have hψsub : (Proposition.box ψ) ∈ modalSubfmls φ0 :=
        modalUniverse_mem_formula (hb _ hψbox)
      have hψmem : ψ ∈ modalSubfmls (Proposition.box ψ) := by simp [modalSubfmls]
      exact mem_modalUniverse_of hwbound (modalSubfmls_trans hψmem hψsub)
  · simp at heq

/-- Shared closure fact for the `diaNegProps` group propagated by both fresh-world rules
(`diamondPos`, `Rules.lean:105-113`; `boxNeg`, `Rules.lean:130-138`): each propagated
`F(ψ)@w'` comes from an `F(◇ψ)@w) ∈ b` (encoded as `F((□(ψ→⊥))→⊥)@w`), hence `ψ` is a
subformula of `φ0`. Factored out since the `diaNegProps` construction is byte-identical
between the two rules. -/
private lemma diaNegProps_outputs_subset (φ0 : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hwbound : modalNextWorld b ≤ modalWorldBound φ0) :
    ∀ x ∈ b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .imp (.box (.imp ψ .bot)) .bot =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none),
    x ∈ modalUniverse φ0 := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨sf', hsf'mem, heq⟩ := hx
  split at heq
  · split at heq
    · rename_i ψ hform
      split at heq
      · simp at heq
      · simp only [Option.some.injEq] at heq
        subst heq
        have hψsub : (Proposition.imp (Proposition.box (Proposition.imp ψ Proposition.bot))
            Proposition.bot) ∈ modalSubfmls φ0 := by
          have hmem := modalUniverse_mem_formula (hb sf' hsf'mem)
          rwa [hform] at hmem
        have hψmem : ψ ∈ modalSubfmls (Proposition.imp (Proposition.box (Proposition.imp ψ
            Proposition.bot)) Proposition.bot) := by simp [modalSubfmls]
        exact mem_modalUniverse_of hwbound (modalSubfmls_trans hψmem hψsub)
    · simp at heq
  · simp at heq

/-- `diamondPos`: `T(◇φ)@w = T((□(φ→⊥))→⊥)@w` creates a fresh world `w' = modalNextWorld b`
and emits three groups at `w'` (`Rules.lean:91-114`): the witness `T(φ)@w'`, propagated
box-positives `T(ψ)@w'` (from `T(□ψ)@w ∈ b`), and propagated diamond-negatives `F(ψ)@w'`
(from `F(◇ψ)@w ∈ b`). All three groups stay inside `U(φ0)` given the branch invariant `hb`,
the source membership `hsf`, and the world-bound hypothesis `hW` (consumed for the fresh
label `w' ≤ W`). -/
lemma modalApplyOne_diamondPos_outputs_subset
    (φ0 : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hsf : (⟨.pos, .imp (.box (.imp φ .bot)) .bot, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    ∀ x ∈ ((⟨.pos, φ, modalNextWorld b⟩ :
        SignedFormula (Proposition Atom) WorldIndex) ::
      (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex :=
            ⟨.pos, ψ, modalNextWorld b⟩
          if b.any (· == sf') then none else some sf'
        else none) ++
      b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .imp (.box (.imp ψ .bot)) .bot =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none)),
    x ∈ modalUniverse φ0 := by
  have hwbound : modalNextWorld b ≤ modalWorldBound φ0 := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot))
      Proposition.bot) ∈ modalSubfmls φ0 :=
    modalUniverse_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls
      (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot))
        Proposition.bot) := by simp [modalSubfmls]
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hbox) | hdia
  · exact mem_modalUniverse_of hwbound (modalSubfmls_trans hφmem hsrc)
  · exact boxProps_outputs_subset φ0 b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset φ0 b w hb hwbound x hdia

/-- `boxNeg`: `F(□φ)@w` creates a fresh world `w' = modalNextWorld b` and emits three
groups at `w'` (`Rules.lean:117-139`): the witness `F(φ)@w'`, propagated box-positives
`T(ψ)@w'` (from `T(□ψ)@w ∈ b`), and propagated diamond-negatives `F(ψ)@w'` (from
`F(◇ψ)@w ∈ b`). Identical structure to `modalApplyOne_diamondPos_outputs_subset` except
the witness is directly `φ` (a subformula of `.box φ` itself, no diamond-encoding to
unwind) and negatively signed. -/
lemma modalApplyOne_boxNeg_outputs_subset
    (φ0 : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hsf : (⟨.neg, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    ∀ x ∈ ((⟨.neg, φ, modalNextWorld b⟩ :
        SignedFormula (Proposition Atom) WorldIndex) ::
      (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex :=
            ⟨.pos, ψ, modalNextWorld b⟩
          if b.any (· == sf') then none else some sf'
        else none) ++
      b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .imp (.box (.imp ψ .bot)) .bot =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none)),
    x ∈ modalUniverse φ0 := by
  have hwbound : modalNextWorld b ≤ modalWorldBound φ0 := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.box φ) ∈ modalSubfmls φ0 := modalUniverse_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls (Proposition.box φ) := by simp [modalSubfmls]
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hbox) | hdia
  · exact mem_modalUniverse_of hwbound (modalSubfmls_trans hφmem hsrc)
  · exact boxProps_outputs_subset φ0 b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset φ0 b w hb hwbound x hdia

omit [DecidableEq Atom] [Hashable Atom] in
/-- Bridge from `Accessibility.successorsOf` membership to `hasEdge`: if `w'` is returned by
`successorsOf acc w`, the edge `w → w'` is recorded in `acc`. Needed to connect the
`boxPos`/`diamondNeg` closure lemmas (P1a, which only give `x.label ∈ acc.successorsOf w`)
to `accFreshInv`'s edge-indexed bound. -/
private lemma mem_successorsOf_hasEdge {acc : Accessibility} {w w' : WorldIndex}
    (h : w' ∈ acc.successorsOf w) : acc.hasEdge w w' = true := by
  simp only [Accessibility.successorsOf, List.mem_filterMap] at h
  obtain ⟨⟨src, tgt⟩, hmem, heq⟩ := h
  split at heq
  · rename_i hsrc
    simp only [Option.some.injEq] at heq
    simp only [Accessibility.hasEdge, List.any_eq_true, Bool.and_eq_true]
    exact ⟨(src, tgt), hmem, hsrc, by rw [beq_iff_eq]; exact heq⟩
  · simp at heq

/-- **Top-level dispatch**: every signed formula emitted by `modalApplyOne sf b acc` stays
inside `U(φ0)`, given: the branch invariant `hb`, the source membership `hsf`, the
freshness invariant `hInv` (bounding `acc`'s recorded successors by `modalMaxWorld b`, needed
for the `boxPos`/`diamondNeg` cases which only known `x.label ∈ acc.successorsOf w`), and the
world-bound hypothesis `hW`. Dispatches over the five `modalApplyOne` outcomes: propositional
rules (`modalApplyOne_prop_outputs_subset`), `boxPos`/`diamondNeg`
(`modalApplyOne_boxPos_outputs_subset`/`modalApplyOne_diamondNeg_outputs_subset`, P1a),
`diamondPos`/`boxNeg` (this phase's two lemmas above), and `notApplicable` (trivial). -/
lemma modalApplyOne_outputs_subset
    (φ0 : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0) (hsf : sf ∈ b)
    (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    (match (modalApplyOne sf b acc).fst with
      | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
      | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverse φ0
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
      | .notApplicable => True) := by
  have hsfU : sf ∈ modalUniverse φ0 := hb sf hsf
  have hprop := modalApplyOne_prop_outputs_subset sf
  unfold modalApplyOne
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · simp only [hpa, if_true]
    rcases hpr : tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
      formulas | branches | formulas | -
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzform, hzlabel⟩ := hprop z hz
      refine mem_modalUniverse_of' ?_ (modalSubfmls_trans hzform (modalUniverse_mem_formula hsfU))
      rw [hzlabel]; exact modalUniverse_mem_label hsfU
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzform, hzlabel⟩ := hprop z hz
      refine mem_modalUniverse_of' ?_ (modalSubfmls_trans hzform (modalUniverse_mem_formula hsfU))
      rw [hzlabel]; exact modalUniverse_mem_label hsfU
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzform, hzlabel⟩ := hprop z hz
      refine mem_modalUniverse_of' ?_ (modalSubfmls_trans hzform (modalUniverse_mem_formula hsfU))
      rw [hzlabel]; exact modalUniverse_mem_label hsfU
    · rw [hpr] at hpa
      simp [RuleResult.isApplicable] at hpa
  · rw [if_neg hpa]
    obtain ⟨s, ff, l⟩ := sf
    rcases s with _ | _
    · rcases ff with _ | _ | ⟨a, c⟩ | φ
      · simp
      · simp
      · rcases a with _ | _ | ⟨a2, a3⟩ | a4
        · simp
        · simp
        · simp
        · rcases a4 with _ | _ | ⟨a5, a6⟩ | a7
          · simp
          · simp
          · rcases a6 with _ | _ | ⟨_, _⟩ | _
            · simp
            · rcases c with _ | _ | ⟨_, _⟩ | _
              · simp
              · dsimp only
                exact modalApplyOne_diamondPos_outputs_subset φ0 b a5 l hb hsf hW
              · simp
              · simp
            · simp
            · simp
          · simp
      · dsimp only
        by_cases hemp : (boxPropagation b acc φ l).isEmpty = true
        · simp only [if_pos hemp]
        · simp only [if_neg hemp]
          intro x hx
          obtain ⟨hxform, hxsucc⟩ := modalApplyOne_boxPos_outputs_subset b acc φ l x hx
          have hedge : acc.hasEdge l x.label = true := mem_successorsOf_hasEdge hxsucc
          have hxlt := (hInv l x.label hedge).2
          have hxle : x.label ≤ modalMaxWorld b := Nat.lt_succ_iff.mp hxlt
          exact mem_modalUniverse_of' (Nat.le_of_lt (Nat.lt_of_le_of_lt hxle hW))
            (modalSubfmls_trans hxform (modalUniverse_mem_formula hsfU))
    · rcases ff with _ | _ | ⟨a, c⟩ | φ
      · simp
      · simp
      · rcases a with _ | _ | ⟨a2, a3⟩ | a4
        · simp
        · simp
        · simp
        · rcases a4 with _ | _ | ⟨a5, a6⟩ | a7
          · simp
          · simp
          · rcases a6 with _ | _ | ⟨_, _⟩ | _
            · simp
            · rcases c with _ | _ | ⟨_, _⟩ | _
              · simp
              · dsimp only
                by_cases hemp : ((acc.successorsOf l).filterMap (fun w' =>
                    if b.any (· == (⟨.neg, a5, w'⟩ :
                        SignedFormula (Proposition Atom) WorldIndex))
                    then none
                    else some (⟨.neg, a5, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
                  ).isEmpty = true
                · simp only [if_pos hemp]
                · simp only [if_neg hemp]
                  intro x hx
                  obtain ⟨hxform, hxsucc⟩ := modalApplyOne_diamondNeg_outputs_subset b acc a5 l x hx
                  have hedge : acc.hasEdge l x.label = true := mem_successorsOf_hasEdge hxsucc
                  have hxlt := (hInv l x.label hedge).2
                  have hxle : x.label ≤ modalMaxWorld b := Nat.lt_succ_iff.mp hxlt
                  exact mem_modalUniverse_of' (Nat.le_of_lt (Nat.lt_of_le_of_lt hxle hW))
                    (modalSubfmls_trans hxform (modalUniverse_mem_formula hsfU))
              · simp
              · simp
            · simp
            · simp
          · simp
      · dsimp only
        exact modalApplyOne_boxNeg_outputs_subset φ0 b φ l hb hsf hW

/-! ## World-Count Bound (Phase 2 — the CRUX)

This section proves the a-priori world bound `modalWorldBound φ0` is a per-step loop
invariant of `modalStepBranch`. The naive single-step statement (`modalMaxWorld b <
modalWorldBound φ0` alone as loop invariant) is **not sufficient**: a branch could contain
a single not-yet-fired minting formula at label `modalWorldBound φ0 - 1`, satisfying the
naive hypothesis, whose firing mints world `modalWorldBound φ0`, breaching the bound. The
fix (research §6/C3 contingency) is a proof-only **rank map** recording, for each world, a
remaining modal-depth budget, plus a counting potential `modalCap` bounding how many further
worlds a given budget can spawn. `modalCap Sf k` is the exact geometric sum `Σ_{i≤k} Sf^i`,
via the standard `1 + Sf * modalCap Sf (k-1)` recursion (one root plus up to `Sf` subtrees of
budget `k-1`). -/

/-- The exact geometric-sum capacity: `modalCap Sf k = Σ_{i=0}^{k} Sf^i`, the maximum size of
a tree with branching factor `≤ Sf` and depth `≤ k` (root included). Defined recursively
(`1` plus `Sf` copies of the one-shallower capacity) rather than via `Finset.sum` to keep the
per-step potential-drop arithmetic (`modalCap_succ`) a definitional unfold. -/
def modalCap (Sf : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => 1 + Sf * modalCap Sf k

@[simp] lemma modalCap_zero (Sf : Nat) : modalCap Sf 0 = 1 := rfl

lemma modalCap_succ (Sf k : Nat) :
    modalCap Sf (k + 1) = 1 + Sf * modalCap Sf k := rfl

/-- For branching factor `Sf ≥ 2`, the capacity stays strictly below `Sf ^ (k+1)` (with room
`≥ 1`, stated additively to avoid `Nat` truncated-subtraction pitfalls): the exact geometric
sum `Σ_{i≤k} Sf^i` satisfies `Σ + 1 ≤ Sf^{k+1}` once the branching factor is `≥ 2`. -/
lemma modalCap_add_one_le_pow {Sf : Nat} (hSf : 2 ≤ Sf) :
    ∀ k, modalCap Sf k + 1 ≤ Sf ^ (k + 1)
  | 0 => by simp only [modalCap_zero, Nat.zero_add, pow_one]; omega
  | k + 1 => by
    have ih := modalCap_add_one_le_pow hSf k
    have hmul : Sf * (modalCap Sf k + 1) ≤ Sf * Sf ^ (k + 1) :=
      Nat.mul_le_mul_left Sf ih
    have heq : Sf * Sf ^ (k + 1) = Sf ^ (k + 2) := by ring
    have hexpand : Sf * (modalCap Sf k + 1) = Sf * modalCap Sf k + Sf := by ring
    have hkey : Sf * modalCap Sf k + Sf ≤ Sf ^ (k + 2) := by
      rw [← heq, ← hexpand]; exact hmul
    have hsucc : modalCap Sf (k + 1) + 1 = Sf * modalCap Sf k + 2 := by
      rw [modalCap_succ]; ring
    have hgoal : k + 1 + 1 = k + 2 := rfl
    rw [hsucc, hgoal]
    omega

/-- Degenerate branching factor `Sf ≤ 1` forces capacity `1` regardless of `k` when `k = 0`
(the only case this lemma is ever invoked with, since `Sf = 1` forces `modalDepth φ0 = 0` in
the application below). -/
lemma modalCap_zero_le_pow {Sf : Nat} (hSf : 1 ≤ Sf) : modalCap Sf 0 ≤ Sf ^ 1 := by
  simp only [modalCap_zero, pow_one]; omega

/-- Unconditional capacity bound feeding the world-bound proof: `modalCap Sf k ≤ Sf ^ (k+1)`,
for any `Sf ≥ 1` with `Sf = 1 → k = 0` (the only shape that ever arises, since
`Sf(φ0) = 1 → modalDepth φ0 = 0` structurally — see `modalWorldBound`). -/
lemma modalCap_le_pow {Sf k : Nat} (hSf : 1 ≤ Sf) (hdeg : Sf = 1 → k = 0) :
    modalCap Sf k ≤ Sf ^ (k + 1) := by
  rcases Nat.lt_or_ge Sf 2 with hlt | hge
  · have hSf1 : Sf = 1 := by omega
    subst hSf1
    have hk0 : k = 0 := hdeg rfl
    subst hk0
    simpa using modalCap_zero_le_pow (Sf := 1) (le_refl 1)
  · have := modalCap_add_one_le_pow hge k
    omega

/-! ## World-Count Bound (Phase 2 continuation): out-degree and rank-map bookkeeping

The remaining Phase 2 obligations formalize the hand-verified potential-function argument
(see the plan's "Continuation" checklist under Phase 2): a proof-only per-world **rank map**
(remaining modal-depth budget, frozen at world creation as `parent_rank − 1`), an **out-degree**
counter derived from `acc`, and a **potential** `Φ` combining them that offsets `modalMaxWorld`'s
growth exactly. This section is obligations (a)-(c): the supporting invariants. -/

/-- `true` when `sf` matches one of the two fresh-world-minting rule shapes: `diamondPos`'s
T-diamond encoding `T((□(φ→⊥))→⊥)@w` or `boxNeg`'s F-box shape `F(□φ)@w`
(`Rules.lean:91-139`). Firing either shape via `modalApplyOne` creates a brand-new world; all
other shapes (propositional rules, `boxPos`, `diamondNeg`) never touch `acc`. -/
def isMintingShaped (sf : SignedFormula (Proposition Atom) WorldIndex) : Bool :=
  match sf.sign, sf.formula with
  | .pos, .imp (.box (.imp _ .bot)) .bot => true
  | .neg, .box _ => true
  | _, _ => false

/-- Out-degree of world `w`: the number of successors recorded for `w` in `acc`. -/
def outDeg (acc : Accessibility) (w : WorldIndex) : Nat := (acc.successorsOf w).length

omit [Hashable Atom] in
/-- Structural dispatch of `modalApplyOne`'s accessibility output, restated locally (mirrors
the private `modalApplyOne_fresh` in `Soundness.lean:87`, which cannot be imported across
files): the result is either `acc` unchanged, or `acc.addEdge sf.label wsf.label` with a
`.linear` result headed by the fresh witness `wsf`. -/
private lemma modalApplyOne_fresh_local
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (modalApplyOne sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOne sf b acc).fst = RuleResult.linear (wsf :: rest)
      ∧ (modalApplyOne sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  unfold modalApplyOne
  extract_lets w propResult
  repeat' first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl, rfl⟩
    | split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl, rfl⟩
    | (left; simp only [apply_ite Prod.snd, ite_self])

omit [Hashable Atom] in
/-- **P2-obl-a** (precision refinement of the plan's "branch Nodup" shorthand): `modalStepBranch`
preserves `Nodup`-ness of the **expanded set** `e`, not the raw branch `b`. This is the
mathematically load-bearing fact for the out-degree bound (P2-obl-c): `b` itself is NOT
generally `Nodup` (propositional α/β rule outputs, e.g. `andPos`'s `T(φ∧ψ)@w ↦ [T(φ)@w,
T(ψ)@w]`, are emitted unconditionally with no `b`-membership filter, so duplicate branch
entries can arise when `φ` or `ψ` coincides with an already-present formula — unlike the modal
rules, which all filter their outputs against `b`). `e`, by contrast, IS exactly `Nodup`: a
formula is appended to `e` only after the `¬(expanded.any (· == sf))` gate confirms it is not
already present, so every append extends a `Nodup` list by a genuinely-new element. -/
lemma modalStepBranch_preserves_expandedNodup
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hnodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  simp only [modalStepBranch] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfnotmem : sf ∉ e := by
    intro hmem
    exact hexp (by simp only [List.any_eq_true]; exact ⟨sf, hmem, by simp⟩)
  rcases hfstc : (modalApplyOne sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -⟩ := hsf
    intro e' he'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact hnodup
  · rw [hfstc] at hsf; simp at hsf


/-! ## Rank-Map Invariant (Phase 2 continuation, obligation b)

The rank map `rank : WorldIndex → Nat` records each world's remaining modal-depth budget,
frozen at creation as `parent_rank − 1`. Two facts are maintained together: `rank` bounds
every branch formula's modal depth (`rankBound`), and `rank` strictly decreases by exactly 1
across every recorded accessibility edge (`rankEdge`, the "frozen at creation" fact, needed to
transport the bound across `boxPos`/`diamondNeg`'s propagation to *existing* successors). -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Modal depth is monotone under `modalSubfmls`: a structural subformula has no greater
modal depth than the formula it comes from. -/
private lemma modalDepth_le_of_mem_modalSubfmls {ψ φ : Proposition Atom}
    (h : ψ ∈ modalSubfmls φ) : modalDepth ψ ≤ modalDepth φ := by
  induction φ with
  | atom p =>
    simp only [modalSubfmls, List.mem_singleton] at h; subst h; exact le_refl _
  | bot =>
    simp only [modalSubfmls, List.mem_singleton] at h; subst h; exact le_refl _
  | imp a b iha ihb =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | ha) | hb
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega
    · have := ihb hb; simp only [modalDepth]; omega
  | box a iha =>
    simp only [modalSubfmls, List.mem_cons] at h
    rcases h with rfl | ha
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega

/-- Rank bound for the `boxProps` group propagated by both fresh-world rules (shared shape
between `diamondPos` and `boxNeg`, `Rules.lean:97-102`/`123-128`): each propagated `T(ψ)@freshW`
is exactly at label `freshW` and has `modalDepth ψ ≤ rank w − 1`, derived from the source
`T(□ψ)@w ∈ b`'s rank bound via `modalDepth (.box ψ) = 1 + modalDepth ψ ≤ rank w`. -/
private lemma boxProps_rank_bound
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w freshW : WorldIndex)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label) :
    ∀ x ∈ (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, freshW⟩
          if b.any (· == sf') then none else some sf'
        else none),
    x.label = freshW ∧ modalDepth x.formula ≤ rank w - 1 := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨⟨ψ, src⟩, hψsrc, heq⟩ := hx
  by_cases hsw : src == w
  · rw [if_pos hsw] at heq
    by_cases hmem : b.any
        (· == (⟨.pos, ψ, freshW⟩ : SignedFormula (Proposition Atom) WorldIndex))
    · rw [if_pos hmem] at heq; simp at heq
    · rw [if_neg hmem] at heq
      simp only [Option.some.injEq] at heq
      subst heq
      have hψbox : (⟨.pos, .box ψ, src⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := mem_boxPositivesOf hψsrc
      have hdep : modalDepth (Proposition.box ψ) ≤ rank src := hbound _ hψbox
      have hsrcw : src = w := beq_iff_eq.mp hsw
      subst hsrcw
      simp only [modalDepth] at hdep
      refine ⟨rfl, ?_⟩
      simp only [SignedFormula.formula]
      omega
  · rw [if_neg hsw] at heq; simp at heq

/-- Rank bound for the `diaNegProps` group propagated by both fresh-world rules (shared shape
between `diamondPos` and `boxNeg`, `Rules.lean:105-113`/`130-138`): each propagated `F(ψ)@freshW`
is exactly at label `freshW` and has `modalDepth ψ ≤ rank w − 1`, derived from the source
`F(◇ψ)@w ∈ b`'s rank bound via
`modalDepth (.imp (.box (.imp ψ .bot)) .bot) = 1 + modalDepth ψ ≤ rank w`. -/
private lemma diaNegProps_rank_bound
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w freshW : WorldIndex)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label) :
    ∀ x ∈ b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .imp (.box (.imp ψ .bot)) .bot =>
            let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, freshW⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none),
    x.label = freshW ∧ modalDepth x.formula ≤ rank w - 1 := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨sf', hsf'mem, heq⟩ := hx
  split at heq
  · rename_i hcond
    split at heq
    · rename_i ψ hform
      split at heq
      · simp at heq
      · simp only [Option.some.injEq] at heq
        subst heq
        simp only [Bool.and_eq_true] at hcond
        have hlab : sf'.label = w := beq_iff_eq.mp hcond.2
        have hdep : modalDepth sf'.formula ≤ rank w := hlab ▸ hbound _ hsf'mem
        rw [hform] at hdep
        simp only [modalDepth] at hdep
        refine ⟨rfl, ?_⟩
        simp only [SignedFormula.formula]
        omega
    · simp at heq
  · simp at heq

/-- Rank bound for `boxPos`'s output (propagation to *existing* successors, `Rules.lean:83-88`):
`T(□ψ)@w`'s propagated `T(ψ)@w'` (for `w' ∈ acc.successorsOf w`) has `modalDepth ψ ≤ rank w'`,
transported across the recorded edge `w → w'` via the rank-edge invariant. -/
private lemma boxPos_rank_bound
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w)
    (hψbox : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ x ∈ boxPropagation b acc ψ w, modalDepth x.formula ≤ rank x.label := by
  intro x hx
  simp only [boxPropagation, List.mem_filterMap] at hx
  obtain ⟨w', hw', hxeq⟩ := hx
  split at hxeq
  · simp at hxeq
  · simp only [Option.some.injEq] at hxeq
    subst hxeq
    have hedge' : acc.hasEdge w w' = true := mem_successorsOf_hasEdge hw'
    have hdep : modalDepth (Proposition.box ψ) ≤ rank w := hbound _ hψbox
    have hre : rank w' + 1 = rank w := hedge w w' hedge'
    simp only [SignedFormula.formula, modalDepth] at hdep ⊢
    omega

/-- Rank bound for `diamondNeg`'s output (propagation to *existing* successors,
`Rules.lean:142-151`): `F(◇φ)@w`'s propagated `F(φ)@w'` (for `w' ∈ acc.successorsOf w`) has
`modalDepth φ ≤ rank w'`, transported across the recorded edge `w → w'`. -/
private lemma diamondNeg_rank_bound
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w)
    (hφdia : (⟨.neg, .imp (.box (.imp φ .bot)) .bot, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ x ∈ (acc.successorsOf w).filterMap (fun w' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf') then none else some sf'),
    modalDepth x.formula ≤ rank x.label := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨w', hw', hxeq⟩ := hx
  split at hxeq
  · simp at hxeq
  · simp only [Option.some.injEq] at hxeq
    subst hxeq
    have hedge' : acc.hasEdge w w' = true := mem_successorsOf_hasEdge hw'
    have hdep : modalDepth (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot))
        Proposition.bot) ≤ rank w := hbound _ hφdia
    have hre : rank w' + 1 = rank w := hedge w w' hedge'
    simp only [SignedFormula.formula, modalDepth] at hdep ⊢
    omega

omit [DecidableEq Atom] [Hashable Atom] in
/-- Decompose membership of an edge in `acc.addEdge w w'`: it is either the new edge or old.
Restated locally (mirrors the private `hasEdge_addEdge_cases` in `Soundness.lean:75`, which
cannot be imported across files). -/
private lemma hasEdge_addEdge_cases_local {acc : Accessibility} {w w' a a' : WorldIndex}
    (h : (acc.addEdge w w').hasEdge a a' = true) :
    (a = w ∧ a' = w') ∨ acc.hasEdge a a' = true := by
  simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hw, hw'⟩ | h
  · exact Or.inl ⟨hw.symm, hw'.symm⟩
  · exact Or.inr h

/-- **P2-obl-b**: given `rank` satisfying the rank-bound and rank-edge invariants pre-step,
`modalStepBranch` produces a `rank'` (agreeing with `rank` off the single fresh point
`modalNextWorld b`, when a world is minted by `diamondPos`/`boxNeg`) satisfying both invariants
on every child branch and the post-step accessibility relation `newAcc`. -/
lemma modalStepBranch_exists_rank'
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hInv : accFreshInv b acc)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ b' ∈ newBs, ∀ x ∈ b', modalDepth x.formula ≤ rank' x.label) ∧
      (∀ w w', newAcc.hasEdge w w' → rank' w' + 1 = rank' w) := by
  simp only [modalStepBranch] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hcases : ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ w w', (modalApplyOne sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
      (match (modalApplyOne sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
        | .branching branches => ∀ x ∈ branches.flatten, modalDepth x.formula ≤ rank' x.label
        | .persistent formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
        | .notApplicable => True) := by
    have hsfd : modalDepth sf.formula ≤ rank sf.label := hbound sf hsfmem
    have hprop := modalApplyOne_prop_outputs_subset sf
    unfold modalApplyOne
    by_cases hpa :
        (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
    · simp only [hpa, if_true]
      refine ⟨rank, fun _ _ => rfl, hedge, ?_⟩
      rcases hpr : tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
        formulas | branches | formulas | -
      · rw [hpr] at hprop
        intro z hz
        obtain ⟨hzform, hzlabel⟩ := hprop z hz
        rw [hzlabel]; exact le_trans (modalDepth_le_of_mem_modalSubfmls hzform) hsfd
      · rw [hpr] at hprop
        intro z hz
        obtain ⟨hzform, hzlabel⟩ := hprop z hz
        rw [hzlabel]; exact le_trans (modalDepth_le_of_mem_modalSubfmls hzform) hsfd
      · rw [hpr] at hprop
        intro z hz
        obtain ⟨hzform, hzlabel⟩ := hprop z hz
        rw [hzlabel]; exact le_trans (modalDepth_le_of_mem_modalSubfmls hzform) hsfd
      · rw [hpr] at hpa
        simp [RuleResult.isApplicable] at hpa
    · rw [if_neg hpa]
      obtain ⟨s, ff, l⟩ := sf
      rcases s with _ | _
      · rcases ff with _ | _ | ⟨a, c⟩ | φ
        · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
        · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
        · rcases a with _ | _ | ⟨a2, a3⟩ | a4
          · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
          · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
          · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
          · rcases a4 with _ | _ | ⟨a5, a6⟩ | a7
            · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
            · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
            · rcases a6 with _ | _ | ⟨_, _⟩ | _
              · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
              · rcases c with _ | _ | ⟨_, _⟩ | _
                · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
                · dsimp only
                  have hllt : l < modalNextWorld b :=
                    Nat.lt_succ_of_le (label_le_modalMaxWorld hsfmem)
                  have hsfd' : 1 + modalDepth a5 ≤ rank l := by
                    have h := hsfd
                    simp only [SignedFormula.formula, SignedFormula.label, modalDepth] at h
                    omega
                  refine ⟨Function.update rank (modalNextWorld b) (rank l - 1),
                    fun w hw => Function.update_of_ne hw _ _, ?_, ?_⟩
                  · intro w w' hw'
                    rcases hasEdge_addEdge_cases_local hw' with ⟨rfl, rfl⟩ | hold
                    · rw [Function.update_self, Function.update_of_ne hllt.ne]
                      omega
                    · rw [Function.update_of_ne (hInv w w' hold).1.ne,
                          Function.update_of_ne (hInv w w' hold).2.ne]
                      exact hedge w w' hold
                  · intro x hx
                    simp only [List.mem_cons, List.mem_append] at hx
                    rcases hx with (rfl | hx) | hx
                    · simp only [SignedFormula.formula, SignedFormula.label, Function.update_self]
                      omega
                    · obtain ⟨hxlab, hxdep⟩ :=
                        boxProps_rank_bound b l (modalNextWorld b) rank hbound x hx
                      rw [hxlab, Function.update_self]
                      exact hxdep
                    · obtain ⟨hxlab, hxdep⟩ :=
                        diaNegProps_rank_bound b l (modalNextWorld b) rank hbound x hx
                      rw [hxlab, Function.update_self]
                      exact hxdep
                · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
                · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
              · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
              · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
            · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
        · dsimp only
          by_cases hemp : (boxPropagation b acc φ l).isEmpty = true
          · simp only [if_pos hemp]
            exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
          · simp only [if_neg hemp]
            have hψbox : (⟨.pos, Proposition.box φ, l⟩ :
                SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfmem
            exact ⟨rank, fun _ _ => rfl, hedge,
              boxPos_rank_bound b acc φ l rank hbound hedge hψbox⟩
      · rcases ff with _ | _ | ⟨a, c⟩ | φ
        · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
        · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
        · rcases a with _ | _ | ⟨a2, a3⟩ | a4
          · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
          · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
          · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
          · rcases a4 with _ | _ | ⟨a5, a6⟩ | a7
            · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
            · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
            · rcases a6 with _ | _ | ⟨_, _⟩ | _
              · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
              · rcases c with _ | _ | ⟨_, _⟩ | _
                · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
                · dsimp only
                  have hφdia : (⟨.neg, Proposition.imp (Proposition.box
                      (Proposition.imp a5 Proposition.bot)) Proposition.bot, l⟩ :
                      SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfmem
                  by_cases hemp : ((acc.successorsOf l).filterMap (fun w' =>
                      if b.any (· == (⟨.neg, a5, w'⟩ :
                          SignedFormula (Proposition Atom) WorldIndex))
                      then none
                      else some (⟨.neg, a5, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
                    ).isEmpty = true
                  · simp only [if_pos hemp]
                    exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
                  · simp only [if_neg hemp]
                    exact ⟨rank, fun _ _ => rfl, hedge,
                      diamondNeg_rank_bound b acc a5 l rank hbound hedge hφdia⟩
                · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
                · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
              · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
              · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
            · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
        · dsimp only
          have hllt : l < modalNextWorld b :=
                    Nat.lt_succ_of_le (label_le_modalMaxWorld hsfmem)
          have hsfd' : 1 + modalDepth φ ≤ rank l := by
            have h := hsfd
            simp only [SignedFormula.formula, SignedFormula.label, modalDepth] at h
            omega
          refine ⟨Function.update rank (modalNextWorld b) (rank l - 1),
            fun w hw => Function.update_of_ne hw _ _, ?_, ?_⟩
          · intro w w' hw'
            rcases hasEdge_addEdge_cases_local hw' with ⟨rfl, rfl⟩ | hold
            · rw [Function.update_self, Function.update_of_ne hllt.ne]
              omega
            · rw [Function.update_of_ne (hInv w w' hold).1.ne,
                  Function.update_of_ne (hInv w w' hold).2.ne]
              exact hedge w w' hold
          · intro x hx
            simp only [List.mem_cons, List.mem_append] at hx
            rcases hx with (rfl | hx) | hx
            · simp only [SignedFormula.formula, SignedFormula.label, Function.update_self]
              omega
            · obtain ⟨hxlab, hxdep⟩ :=
                boxProps_rank_bound b l (modalNextWorld b) rank hbound x hx
              rw [hxlab, Function.update_self]
              exact hxdep
            · obtain ⟨hxlab, hxdep⟩ :=
                diaNegProps_rank_bound b l (modalNextWorld b) rank hbound x hx
              rw [hxlab, Function.update_self]
              exact hxdep

  obtain ⟨rank', hragree, hredge, hrmatch⟩ := hcases
  have hnewAcc : newAcc = (modalApplyOne sf b acc).snd := by
    rcases hfstc : (modalApplyOne sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.2.2.symm
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.2.2.symm
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp at hsf
  refine ⟨rank', hragree, ?_, hnewAcc ▸ hredge⟩
  rcases hfstc : (modalApplyOne sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf hrmatch
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrmatch x hx
    · have hxlab : x.label ≠ modalNextWorld b :=
        Nat.ne_of_lt (Nat.lt_succ_of_le (label_le_modalMaxWorld hx))
      rw [hragree x.label hxlab]
      exact hbound x hx
  · rw [hfstc] at hsf hrmatch
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrmatch x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)
    · have hxlab : x.label ≠ modalNextWorld b :=
        Nat.ne_of_lt (Nat.lt_succ_of_le (label_le_modalMaxWorld hx))
      rw [hragree x.label hxlab]
      exact hbound x hx
  · rw [hfstc] at hsf hrmatch
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hrmatch x hx
    · have hxlab : x.label ≠ modalNextWorld b :=
        Nat.ne_of_lt (Nat.lt_succ_of_le (label_le_modalMaxWorld hx))
      rw [hragree x.label hxlab]
      exact hbound x hx
  · rw [hfstc] at hsf; simp at hsf

end Cslib.Logic.Modal.Tableau

end
