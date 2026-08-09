/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Nodup
import Batteries.Data.List.Perm
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Cslib.Foundations.Logic.Tableau.Measure
public import Cslib.Logics.Modal.Tableau.Completeness
public import Cslib.Logics.Modal.Tableau.SoundnessStep
public import Cslib.Logics.Modal.Tableau.Saturation
public import Cslib.Logics.Modal.Tableau.Support.Accessibility
public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds

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

/-- Structural subformula list of a `Proposition Atom` (native `and`/`or`/`box`/`diamond`
recursion). Every node of `φ`'s syntax tree contributes exactly one entry. -/
def modalSubfmls : Proposition Atom → List (Proposition Atom)
  | .atom p  => [.atom p]
  | .bot     => [.bot]
  | .imp a b => .imp a b :: modalSubfmls a ++ modalSubfmls b
  | .and a b => .and a b :: modalSubfmls a ++ modalSubfmls b
  | .or a b  => .or a b :: modalSubfmls a ++ modalSubfmls b
  | .box a   => .box a :: modalSubfmls a
  | .diamond a => .diamond a :: modalSubfmls a

omit [DecidableEq Atom] [Hashable Atom] in
/-- The subformula list has length at most `2 * modalComplexity φ + 1`. -/
lemma modalSubfmls_length_le (φ : Proposition Atom) :
    (modalSubfmls φ).length ≤ 2 * modalComplexity φ + 1 := by
  induction φ with
  | atom p => simp [modalSubfmls]
  | bot => simp [modalSubfmls]
  | imp a b iha ihb =>
    simp only [modalSubfmls, List.length_cons, List.length_append, modalComplexity_imp]
    omega
  | and a b iha ihb =>
    simp only [modalSubfmls, List.length_cons, List.length_append, modalComplexity_and]
    omega
  | or a b iha ihb =>
    simp only [modalSubfmls, List.length_cons, List.length_append, modalComplexity_or]
    omega
  | box a iha =>
    simp only [modalSubfmls, List.length_cons, modalComplexity_box]
    omega
  | diamond a iha =>
    simp only [modalSubfmls, List.length_cons, modalComplexity_diamond]
    omega

/-- Modal (box/diamond-nesting) depth of a `Proposition Atom`: `box`/`diamond` add one,
`imp`/`and`/`or` take the max of their two sub-depths (`diamond` is native, and
counts toward depth exactly like `box` since it also creates a fresh world in the tableau). -/
def modalDepth : Proposition Atom → Nat
  | .atom _ => 0
  | .bot => 0
  | .imp a b => max (modalDepth a) (modalDepth b)
  | .and a b => max (modalDepth a) (modalDepth b)
  | .or a b => max (modalDepth a) (modalDepth b)
  | .box a => 1 + modalDepth a
  | .diamond a => 1 + modalDepth a

omit [DecidableEq Atom] [Hashable Atom] in
/-- Modal depth is bounded by structural complexity. -/
lemma modalDepth_le_complexity (φ : Proposition Atom) :
    modalDepth φ ≤ modalComplexity φ := by
  induction φ with
  | atom p => simp [modalDepth]
  | bot => simp [modalDepth]
  | imp a b iha ihb =>
    simp only [modalDepth, modalComplexity_imp]
    omega
  | and a b iha ihb =>
    simp only [modalDepth, modalComplexity_and]
    omega
  | or a b iha ihb =>
    simp only [modalDepth, modalComplexity_or]
    omega
  | box a iha =>
    simp only [modalDepth, modalComplexity_box]
    omega
  | diamond a iha =>
    simp only [modalDepth, modalComplexity_diamond]
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

omit [DecidableEq Atom] [Hashable Atom] in
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

omit [Hashable Atom] in
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

/-! ## Subformula-Closure: World-Preserving Rules

This section proves that formulas emitted by the propositional (α/β) rules, `boxPos`, and
`diamondNeg` — the three rule kinds that do NOT mint a fresh world — are structural
subformulas of the source formula, at a world label that is either unchanged or an existing
successor. This is the closure fact needed for the rule kinds that cannot breach the world
bound, so no world-bound hypothesis is consumed here. The two fresh-world-minting rules
(`diamondPos`, `boxNeg`) and the top-level dispatch lemma are handled in the next section. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every `Proposition Atom` is a member of its own structural subformula list (the list
always begins with the formula itself). Marked `@[simp]` so it discharges nested
`modalSubfmls` membership goals as a rewrite. -/
@[simp]
lemma modalSubfmls_self_mem (φ : Proposition Atom) : φ ∈ modalSubfmls φ := by
  cases φ <;> simp [modalSubfmls]

omit [DecidableEq Atom] [Hashable Atom] in
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
            simp only [List.mem_cons,
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

omit [Hashable Atom] in
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

omit [Hashable Atom] in
/-- `diamondNeg`: `F(◇φ)@w` emits `F(φ)@w'` for each recorded successor `w'` of `w`
(`Rules.lean:144-153`). Every emitted formula's formula-component is `φ`, a structural
subformula of the native source formula `◇φ`, at a world label that is an existing recorded
successor of `w`. `diamond` is a native constructor, so `negOf?` does not match
this shape and this rule arm is the sole dispatch path for `F(◇φ)@w`. -/
lemma modalApplyOne_diamondNeg_outputs_subset
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ (acc.successorsOf w).filterMap (fun w' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf') then none else some sf'),
      x.formula ∈ modalSubfmls (Proposition.diamond φ) ∧
        x.label ∈ acc.successorsOf w := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨w', hw', hxeq⟩ := hx
  split at hxeq
  · simp at hxeq
  · simp only [Option.some.injEq] at hxeq
    subst hxeq
    exact ⟨by simp [modalSubfmls], hw'⟩

/-! ## Subformula-Closure: Fresh-World Rules and Top Dispatch

This section proves closure for the two fresh-world-minting linear rules (`diamondPos`,
`boxNeg`, `Rules.lean:91-139`), which consume the world-bound hypothesis to show the freshly
minted world label stays inside `U(φ0)`, and assembles the top-level dispatch lemma
`modalApplyOne_outputs_subset` by case analysis over `modalApplyOne`. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Transitivity of `modalSubfmls`: a subformula of a subformula is a subformula. Needed
because the fresh-world rules' propagated groups (`boxProps`, `diaNegProps`) derive their
subformula bound from *other* branch members via the branch invariant, not from the source
formula directly, so a two-step subformula chain must be composed. -/
lemma modalSubfmls_trans {a b c : Proposition Atom}
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
  | and x y ihx ihy =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at hbc
    rcases hbc with (rfl | hx) | hy
    · exact hab
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihx hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihy hy))
  | or x y ihx ihy =>
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
  | diamond x ihx =>
    simp only [modalSubfmls, List.mem_cons] at hbc
    rcases hbc with rfl | hx
    · exact hab
    · exact List.mem_cons_of_mem _ (ihx hx)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Constructor direction for `modalUniverse` membership: a signed formula with any sign,
a subformula of `φ0`, at a world label within the bound, is in `U(φ0)`. -/
lemma mem_modalUniverse_of {φ0 : Proposition Atom} {s : Sign} {φ : Proposition Atom}
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
lemma modalUniverse_mem_formula {φ0 : Proposition Atom}
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

omit [Hashable Atom] in
/-- Shared closure fact for the `boxProps` group propagated by both fresh-world rules
(`diamondPos`, `Rules.lean:97-102`; `boxNeg`, `Rules.lean:123-128`): each propagated
`T(ψ)@w'` comes from a `T(□ψ)@w ∈ b`, hence `ψ` is a subformula of `φ0`. Factored out since
the `boxProps` construction is byte-identical between the two rules. -/
lemma boxProps_outputs_subset (φ0 : Proposition Atom)
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

omit [Hashable Atom] in
/-- Shared closure fact for the `diaNegProps` group propagated by both fresh-world rules
(`diamondPos`, `Rules.lean:107-115`; `boxNeg`, `Rules.lean:132-140`): each propagated
`F(ψ)@w'` comes from an `F(◇ψ)@w) ∈ b` (native `diamond` constructor), hence `ψ`
is a subformula of `φ0`. Factored out since the `diaNegProps` construction is byte-identical
between the two rules. -/
lemma diaNegProps_outputs_subset (φ0 : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hwbound : modalNextWorld b ≤ modalWorldBound φ0) :
    ∀ x ∈ b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .diamond ψ =>
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
        have hψsub : (Proposition.diamond ψ) ∈ modalSubfmls φ0 := by
          have hmem := modalUniverse_mem_formula (hb sf' hsf'mem)
          rwa [hform] at hmem
        have hψmem : ψ ∈ modalSubfmls (Proposition.diamond ψ) := by simp [modalSubfmls]
        exact mem_modalUniverse_of hwbound (modalSubfmls_trans hψmem hψsub)
    · simp at heq
  · simp at heq

omit [Hashable Atom] in
/-- `diamondPos`: `T(◇φ)@w` creates a fresh world `w' = modalNextWorld b` and emits three
groups at `w'` (`Rules.lean:93-116`): the witness `T(φ)@w'`, propagated box-positives
`T(ψ)@w'` (from `T(□ψ)@w ∈ b`), and propagated diamond-negatives `F(ψ)@w'`
(from `F(◇ψ)@w ∈ b`). All three groups stay inside `U(φ0)` given the branch invariant `hb`,
the source membership `hsf`, and the world-bound hypothesis `hW` (consumed for the fresh
label `w' ≤ W`). `diamond` is a native constructor, so the witness is directly a
subformula of `◇φ` (no encoding to unwind). -/
lemma modalApplyOne_diamondPos_outputs_subset
    (φ0 : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hsf : (⟨.pos, .diamond φ, w⟩ :
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
          | .diamond ψ =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none)),
    x ∈ modalUniverse φ0 := by
  have hwbound : modalNextWorld b ≤ modalWorldBound φ0 := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ0 :=
    modalUniverse_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) := by simp [modalSubfmls]
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hbox) | hdia
  · exact mem_modalUniverse_of hwbound (modalSubfmls_trans hφmem hsrc)
  · exact boxProps_outputs_subset φ0 b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset φ0 b w hb hwbound x hdia

omit [Hashable Atom] in
/-- `boxNeg`: `F(□φ)@w` creates a fresh world `w' = modalNextWorld b` and emits three
groups at `w'` (`Rules.lean:119-141`): the witness `F(φ)@w'`, propagated box-positives
`T(ψ)@w'` (from `T(□ψ)@w ∈ b`), and propagated diamond-negatives `F(ψ)@w'` (from
`F(◇ψ)@w ∈ b`). Identical structure to `modalApplyOne_diamondPos_outputs_subset` except
the witness is directly `φ` (a subformula of `.box φ` itself) and negatively signed. -/
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
          | .diamond ψ =>
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

omit [Hashable Atom] in
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
    · -- pos: only `.box`/`.diamond` match a K-rule arm; the rest fall through to
      -- `modalApplyOne`'s `_, _ => .notApplicable` catch-all regardless of `hpa`
      -- (`and`/`or`/`imp` are all native/non-diamond-encoded, so no disambiguation is needed).
      rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
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
      · dsimp only
        exact modalApplyOne_diamondPos_outputs_subset φ0 b φ l hb hsf hW
    · -- neg: symmetric to the `pos` case above.
      rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · simp
      · simp
      · simp
      · simp
      · simp
      · dsimp only
        exact modalApplyOne_boxNeg_outputs_subset φ0 b φ l hb hsf hW
      · dsimp only
        by_cases hemp : ((acc.successorsOf l).filterMap (fun w' =>
            if b.any (· == (⟨.neg, φ, w'⟩ :
                SignedFormula (Proposition Atom) WorldIndex))
            then none
            else some (⟨.neg, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
          ).isEmpty = true
        · simp only [if_pos hemp]
        · simp only [if_neg hemp]
          intro x hx
          obtain ⟨hxform, hxsucc⟩ := modalApplyOne_diamondNeg_outputs_subset b acc φ l x hx
          have hedge : acc.hasEdge l x.label = true := mem_successorsOf_hasEdge hxsucc
          have hxlt := (hInv l x.label hedge).2
          have hxle : x.label ≤ modalMaxWorld b := Nat.lt_succ_iff.mp hxlt
          exact mem_modalUniverse_of' (Nat.le_of_lt (Nat.lt_of_le_of_lt hxle hW))
            (modalSubfmls_trans hxform (modalUniverse_mem_formula hsfU))

/-! ## World-Count Bound — the Crux

This section proves the a-priori world bound `modalWorldBound φ0` is a per-step loop
invariant of `modalStepBranch`. The naive single-step statement (`modalMaxWorld b <
modalWorldBound φ0` alone as loop invariant) is **not sufficient**: a branch could contain
a single not-yet-fired minting formula at label `modalWorldBound φ0 - 1`, satisfying the
naive hypothesis, whose firing mints world `modalWorldBound φ0`, breaching the bound. The
fix is a proof-only **rank map** recording, for each world, a
remaining modal-depth budget, plus a counting potential `geomCap` (shared,
`Cslib.Foundations.Logic.Tableau.Measure`) bounding how many further worlds a given budget can
spawn. `geomCap Sf k` is the exact geometric sum `Σ_{i≤k} Sf^i`, via the standard
`1 + Sf * geomCap Sf (k-1)` recursion (one root plus up to `Sf` subtrees of budget `k-1`). -/

/-! ## World-Count Bound: Out-Degree and Rank-Map Bookkeeping

This section formalizes the hand-verified potential-function argument: a proof-only per-world
**rank map** (remaining modal-depth budget, frozen at world creation as `parent_rank − 1`), an
**out-degree** counter derived from `acc`, and a **potential** `Φ` combining them that offsets
`modalMaxWorld`'s growth exactly. This section covers obligations (a)-(c): the supporting
invariants. -/

/-- `true` when `sf` matches a rule shape that actually mints a fresh world at runtime:
`boxNeg`'s F-box shape `F(□φ)@w` (`Rules.lean:119-141`) or `diamondPos`'s T-diamond shape
`T(◇φ)@w` (`Rules.lean:93-116`). `diamond` is a native constructor, so `diamondPos`
genuinely fires (and mints `acc.addEdge w (modalNextWorld b)`, exactly like `boxNeg`).
Neither shape is matched by any propositional rule (`.box`/`.diamond` are top-level
constructors distinct from every prop-rule pattern's `.imp`/`.and`/`.or`-headed shape), so
together they correctly track every `acc`-mutating step. -/
def isMintingShaped (sf : SignedFormula (Proposition Atom) WorldIndex) : Bool :=
  match sf.sign, sf.formula with
  | .neg, .box _ => true
  | .pos, .diamond _ => true
  | _, _ => false

/-- Out-degree of world `w`: the number of successors recorded for `w` in `acc`. -/
def outDeg (acc : Accessibility) (w : WorldIndex) : Nat := (acc.successorsOf w).length

omit [Hashable Atom] in
/-- Structural dispatch of `modalApplyOne`'s accessibility output, restated locally (mirrors
the private `modalApplyOne_fresh` in `Soundness.lean:87`, which cannot be imported across
files): the result is either `acc` unchanged, or `acc.addEdge sf.label wsf.label` with a
`.linear` result headed by the fresh witness `wsf`. Not `private`: reused by
`GenericDriver.lean`'s `modalApplyOne_spec` to witness the
`RuleApplicationSpec.freshLocal` field. -/
lemma modalApplyOne_fresh_local
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

/-- **Generic form**: `modalStepBranchGen apply` preserves `Nodup`-ness of the
expanded set `e`, for **any** `apply : RuleApply Atom` -- fully rule-agnostic, no per-call
obligation about `apply` needed (only the top-level `RuleResult`-constructor shape matters).
`modalStepBranch_preserves_expandedNodup` (K) is the trivial instantiation at
`apply := modalApplyOne`. -/
lemma modalStepBranch_preserves_expandedNodup_gen
    (apply : RuleApply Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hnodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfnotmem : sf ∉ e := by
    intro hmem
    exact hexp (by simp only [List.any_eq_true]; exact ⟨sf, hmem, by simp⟩)
  rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
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

/-- **P2-obl-a** (a precision refinement distinguishing the expanded set from the raw branch):
`modalStepBranch` preserves `Nodup`-ness of the **expanded set** `e`, not the raw branch `b`.
This is the mathematically load-bearing fact for the out-degree bound (P2-obl-c): `b` itself is NOT
generally `Nodup` (propositional α/β rule outputs, e.g. `andPos`'s `T(φ∧ψ)@w ↦ [T(φ)@w,
T(ψ)@w]`, are emitted unconditionally with no `b`-membership filter, so duplicate branch
entries can arise when `φ` or `ψ` coincides with an already-present formula — unlike the modal
rules, which all filter their outputs against `b`). `e`, by contrast, IS exactly `Nodup`: a
formula is appended to `e` only after the `¬(expanded.any (· == sf))` gate confirms it is not
already present, so every append extends a `Nodup` list by a genuinely-new element.
Zero-regression corollary of `modalStepBranch_preserves_expandedNodup_gen` at
`apply := modalApplyOne` via the `modalStepBranch_eq` bridge; statement byte-unchanged. -/
lemma modalStepBranch_preserves_expandedNodup
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hnodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  rw [modalStepBranch_eq] at hstep
  exact modalStepBranch_preserves_expandedNodup_gen modalApplyOne b e acc newBs newExps newAcc
    hstep hnodup


/-! ## Rank-Map Invariant (obligation b)

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
  | and a b iha ihb =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | ha) | hb
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega
    · have := ihb hb; simp only [modalDepth]; omega
  | or a b iha ihb =>
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
  | diamond a iha =>
    simp only [modalSubfmls, List.mem_cons] at h
    rcases h with rfl | ha
    · exact le_refl _
    · have := iha ha; simp only [modalDepth]; omega

omit [Hashable Atom] in
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
      simp only []
      omega
  · rw [if_neg hsw] at heq; simp at heq

omit [Hashable Atom] in
/-- Rank bound for the `diaNegProps` group propagated by both fresh-world rules (shared shape
between `diamondPos` and `boxNeg`, `Rules.lean:107-115`/`132-140`): each propagated `F(ψ)@freshW`
is exactly at label `freshW` and has `modalDepth ψ ≤ rank w − 1`, derived from the source
`F(◇ψ)@w ∈ b`'s rank bound via `modalDepth (.diamond ψ) = 1 + modalDepth ψ ≤ rank w`
(`diamond` is a native constructor). -/
private lemma diaNegProps_rank_bound
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w freshW : WorldIndex)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label) :
    ∀ x ∈ b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .diamond ψ =>
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
        simp only []
        omega
    · simp at heq
  · simp at heq

omit [Hashable Atom] in
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
    simp only [modalDepth] at hdep ⊢
    omega

omit [Hashable Atom] in
/-- Rank bound for `diamondNeg`'s output (propagation to *existing* successors,
`Rules.lean:144-153`): `F(◇φ)@w`'s propagated `F(φ)@w'` (for `w' ∈ acc.successorsOf w`) has
`modalDepth φ ≤ rank w'`, transported across the recorded edge `w → w'` (`diamond`
is a native constructor). -/
private lemma diamondNeg_rank_bound
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w)
    (hφdia : (⟨.neg, .diamond φ, w⟩ :
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
    have hdep : modalDepth (Proposition.diamond φ) ≤ rank w := hbound _ hφdia
    have hre : rank w' + 1 = rank w := hedge w w' hedge'
    simp only [modalDepth] at hdep ⊢
    omega

omit [Hashable Atom] in
/-- **Generic per-call rank-step obligation**: the single-call rank-preservation fact
`modalStepBranch_exists_rank'`'s proof needs about `modalApplyOne` at each firing, extracted as
its own lemma so the surrounding driver-unfolding argument (rule-agnostic: it only inspects the
four `RuleResult` constructor shapes) can be replayed for an abstract `apply` given this fact as
a `RuleApplicationSpec` field (`rankStep`, `GenericDriver.lean`). Witnesses `rank'`, agreeing with
`rank` off the fresh point `modalNextWorld b`, satisfying the rank-edge invariant on
`(modalApplyOne sf b acc).snd` and the rank-bound on `(modalApplyOne sf b acc).fst`'s output. -/
lemma modalApplyOne_rank_step
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hInv : accFreshInv b acc)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) :
    ∃ rank' : WorldIndex → Nat,
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
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · -- box φ (boxPos): propagates to *existing* successors.
        dsimp only
        by_cases hemp : (boxPropagation b acc φ l).isEmpty = true
        · simp only [if_pos hemp]
          exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
        · simp only [if_neg hemp]
          have hψbox : (⟨.pos, Proposition.box φ, l⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfmem
          exact ⟨rank, fun _ _ => rfl, hedge,
            boxPos_rank_bound b acc φ l rank hbound hedge hψbox⟩
      · -- diamond φ (diamondPos): mints a fresh world (native constructor).
        dsimp only
        have hllt : l < modalNextWorld b :=
          Nat.lt_succ_of_le (label_le_modalMaxWorld hsfmem)
        have hsfd' : 1 + modalDepth φ ≤ rank l := by
          have h := hsfd
          simp only [modalDepth] at h
          omega
        refine ⟨Function.update rank (modalNextWorld b) (rank l - 1),
          fun w hw => Function.update_of_ne hw _ _, ?_, ?_⟩
        · intro w w' hw'
          rcases hasEdge_addEdge_cases hw' with ⟨rfl, rfl⟩ | hold
          · rw [Function.update_self, Function.update_of_ne hllt.ne]
            omega
          · rw [Function.update_of_ne (hInv w w' hold).1.ne,
                Function.update_of_ne (hInv w w' hold).2.ne]
            exact hedge w w' hold
        · intro x hx
          simp only [List.mem_cons, List.mem_append] at hx
          rcases hx with (rfl | hx) | hx
          · simp only [Function.update_self]
            omega
          · obtain ⟨hxlab, hxdep⟩ :=
              boxProps_rank_bound b l (modalNextWorld b) rank hbound x hx
            rw [hxlab, Function.update_self]
            exact hxdep
          · obtain ⟨hxlab, hxdep⟩ :=
              diaNegProps_rank_bound b l (modalNextWorld b) rank hbound x hx
            rw [hxlab, Function.update_self]
            exact hxdep
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
      · -- box φ (boxNeg): mints a fresh world, symmetric to diamondPos above.
        dsimp only
        have hllt : l < modalNextWorld b :=
                  Nat.lt_succ_of_le (label_le_modalMaxWorld hsfmem)
        have hsfd' : 1 + modalDepth φ ≤ rank l := by
          have h := hsfd
          simp only [modalDepth] at h
          omega
        refine ⟨Function.update rank (modalNextWorld b) (rank l - 1),
          fun w hw => Function.update_of_ne hw _ _, ?_, ?_⟩
        · intro w w' hw'
          rcases hasEdge_addEdge_cases hw' with ⟨rfl, rfl⟩ | hold
          · rw [Function.update_self, Function.update_of_ne hllt.ne]
            omega
          · rw [Function.update_of_ne (hInv w w' hold).1.ne,
                Function.update_of_ne (hInv w w' hold).2.ne]
            exact hedge w w' hold
        · intro x hx
          simp only [List.mem_cons, List.mem_append] at hx
          rcases hx with (rfl | hx) | hx
          · simp only [Function.update_self]
            omega
          · obtain ⟨hxlab, hxdep⟩ :=
              boxProps_rank_bound b l (modalNextWorld b) rank hbound x hx
            rw [hxlab, Function.update_self]
            exact hxdep
          · obtain ⟨hxlab, hxdep⟩ :=
              diaNegProps_rank_bound b l (modalNextWorld b) rank hbound x hx
            rw [hxlab, Function.update_self]
            exact hxdep
      · -- diamond φ (diamondNeg): propagates to *existing* successors.
        dsimp only
        have hφdia : (⟨.neg, Proposition.diamond φ, l⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfmem
        by_cases hemp : ((acc.successorsOf l).filterMap (fun w' =>
            if b.any (· == (⟨.neg, φ, w'⟩ :
                SignedFormula (Proposition Atom) WorldIndex))
            then none
            else some (⟨.neg, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
          ).isEmpty = true
        · simp only [if_pos hemp]
          exact ⟨rank, fun _ _ => rfl, hedge, trivial⟩
        · simp only [if_neg hemp]
          exact ⟨rank, fun _ _ => rfl, hedge,
            diamondNeg_rank_bound b acc φ l rank hbound hedge hφdia⟩

/-- **Generic form**: given `rank` satisfying the rank-bound and rank-edge
invariants pre-step, `modalStepBranchGen apply` produces a `rank'` (agreeing with `rank` off the
single fresh point `modalNextWorld b`) satisfying both invariants on every child branch and the
post-step accessibility relation `newAcc`, given the per-call rank-step obligation `hRankStep`
(the raw hypothesis underlying `RuleApplicationSpec.rankStep`, spelled out here rather than
bundled, to avoid an import cycle with `GenericDriver.lean`).
`modalStepBranch_exists_rank'` (K) is the trivial instantiation at
`apply := modalApplyOne`, `hRankStep := modalApplyOne_rank_step`. -/
lemma modalStepBranch_exists_rank'_gen
    (apply : RuleApply Atom)
    (hRankStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accFreshInv b acc →
      ∀ (rank : WorldIndex → Nat),
      (∀ x ∈ b, modalDepth x.formula ≤ rank x.label) →
      (∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) →
      ∃ rank' : WorldIndex → Nat,
        (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
        (∀ w w', (apply sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .branching branches => ∀ x ∈ branches.flatten, modalDepth x.formula ≤ rank' x.label
          | .persistent formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .notApplicable => True))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hInv : accFreshInv b acc)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ b' ∈ newBs, ∀ x ∈ b', modalDepth x.formula ≤ rank' x.label) ∧
      (∀ w w', newAcc.hasEdge w w' → rank' w' + 1 = rank' w) := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hcases := hRankStep sf b acc hsfmem hInv rank hbound hedge
  obtain ⟨rank', hragree, hredge, hrmatch⟩ := hcases
  have hnewAcc : newAcc = (apply sf b acc).snd := by
    rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
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
  rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
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

/-- **P2-obl-b**: given `rank` satisfying the rank-bound and rank-edge invariants pre-step,
`modalStepBranch` produces a `rank'` (agreeing with `rank` off the single fresh point
`modalNextWorld b`, when a world is minted by `diamondPos`/`boxNeg`) satisfying both invariants
on every child branch and the post-step accessibility relation `newAcc`. Zero-regression
corollary of `modalStepBranch_exists_rank'_gen` at `apply := modalApplyOne`
via the `modalStepBranch_eq` bridge; statement byte-unchanged. -/
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
  rw [modalStepBranch_eq] at hstep
  exact modalStepBranch_exists_rank'_gen modalApplyOne modalApplyOne_rank_step
    b e acc newBs newExps newAcc hstep hInv rank hbound hedge


/-! ## Out-Degree Bound (obligation c)

`boxNeg` (`F(□φ)@w`) is the **only** rule shape that ever mutates `acc` at runtime (see
`isMintingShaped`'s doc comment for the dead-code argument ruling out `diamondPos`/`diamondNeg`).
This section proves the exact counting correspondence `outDeg acc w = |{formulas in e matching
isMintingShaped at w}|`, then derives `outDeg acc w ≤ Sf` from `e`'s `Nodup`-ness
(`modalStepBranch_preserves_expandedNodup`, P2-obl-a) and the closure fact
`e ⊆ modalUniverse φ0`. -/

omit [DecidableEq Atom] in
omit [Hashable Atom] in
/-- A `isMintingShaped` (i.e. `boxNeg`-shaped, `.neg, .box _`) formula can never fire via a
propositional rule: `.box` is a distinct top-level constructor from every prop-rule pattern's
`.imp`-headed shape, so all 8 `applyPropRule` cases return `notApplicable`. Verified by `rfl`
(a purely structural computation, independent of the box's body). -/
private lemma isMintingShaped_not_prop_applicable
    (sf : SignedFormula (Proposition Atom) WorldIndex) (h : isMintingShaped sf = true) :
    (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable = false := by
  unfold isMintingShaped at h
  obtain ⟨s, ff, l⟩ := sf
  rcases s with _ | _
  · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · simp [tryAllPropRules_pos, modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?,
        RuleResult.isApplicable]
  · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · rfl
    · simp at h

omit [DecidableEq Atom] [Hashable Atom] in
/-- Appending a non-minting-shaped formula to the expanded set leaves the minting-filtered
count unchanged, for every world `w` simultaneously (the predicate ignores the label when
`isMintingShaped` fails). -/
private lemma filter_minting_append_of_not_minting
    (e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex) (w : WorldIndex)
    (h : isMintingShaped sf = false) :
    (e ++ [sf]).filter (fun x => x.label == w && isMintingShaped x) =
      e.filter (fun x => x.label == w && isMintingShaped x) := by
  rw [List.filter_append]
  simp [h]

omit [DecidableEq Atom] [Hashable Atom] in
/-- Appending a minting-shaped formula at label `w` to the expanded set extends the
minting-filtered count at `w` by exactly the singleton `[sf]`. -/
private lemma filter_minting_append_of_minting_at
    (e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (h : isMintingShaped sf = true) :
    (e ++ [sf]).filter (fun x => x.label == sf.label && isMintingShaped x) =
      e.filter (fun x => x.label == sf.label && isMintingShaped x) ++ [sf] := by
  rw [List.filter_append]
  simp [h]

omit [DecidableEq Atom] [Hashable Atom] in
/-- Appending a minting-shaped formula at label `sf.label` to the expanded set leaves the
minting-filtered count at any *other* world `w` unchanged. -/
private lemma filter_minting_append_of_minting_ne
    (e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex) (w : WorldIndex)
    (hw : w ≠ sf.label) :
    (e ++ [sf]).filter (fun x => x.label == w && isMintingShaped x) =
      e.filter (fun x => x.label == w && isMintingShaped x) := by
  rw [List.filter_append]
  have : (sf.label == w) = false := by
    simp only [beq_eq_false_iff_ne]; exact fun h => hw h.symm
  simp [this]

omit [DecidableEq Atom] [Hashable Atom] in
/-- `outDeg` under `addEdge` at the matching source: extends the successor list by exactly the
new target, incrementing `outDeg` by 1. -/
lemma outDeg_addEdge_self (acc : Accessibility) (w wf : WorldIndex) :
    outDeg (acc.addEdge w wf) w = outDeg acc w + 1 := by
  simp [outDeg, Accessibility.successorsOf, Accessibility.addEdge]

omit [DecidableEq Atom] [Hashable Atom] in
/-- `outDeg` under `addEdge` is unchanged at any world other than the edge's source. -/
lemma outDeg_addEdge_ne (acc : Accessibility) (w wf w' : WorldIndex) (h : w' ≠ w) :
    outDeg (acc.addEdge w wf) w' = outDeg acc w' := by
  simp only [outDeg, Accessibility.successorsOf, Accessibility.addEdge, List.filterMap_cons]
  have : (w == w') = false := by simp only [beq_eq_false_iff_ne]; exact fun heq => h heq.symm
  simp [this]


omit [Hashable Atom] in
/-- **Generic per-call outDeg-step obligation**: the single-call outDeg/expanded-set
counting fact `modalStepBranch_preserves_outDegEq`'s proof needs about `modalApplyOne` at each
firing, extracted as its own lemma so the surrounding driver-unfolding argument (rule-agnostic:
it only inspects the four `RuleResult` constructor shapes) can be replayed for an abstract
`apply` given this fact as a `RuleApplicationSpec` field (`outDegStep`, `GenericDriver.lean`). -/
lemma modalApplyOne_outDeg_step
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (houtdeg : ∀ w, outDeg acc w =
      (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ w, outDeg (modalApplyOne sf b acc).snd w =
      (List.filter (fun x => x.label == w && isMintingShaped x)
        (match (modalApplyOne sf b acc).fst with
          | .linear _ => e ++ [sf]
          | .branching _ => e ++ [sf]
          | .persistent _ => e
          | .notApplicable =>
            (e : List (SignedFormula (Proposition Atom) WorldIndex)))).length := by
  intro w
  unfold modalApplyOne
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · simp only [hpa, if_true]
    have hnm : isMintingShaped sf = false := by
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      have hcontra := isMintingShaped_not_prop_applicable sf hc
      rw [hcontra] at hpa
      simp at hpa
    rcases hpr : tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
      formulas | branches | formulas | -
    · rw [filter_minting_append_of_not_minting e sf w hnm]; exact houtdeg w
    · rw [filter_minting_append_of_not_minting e sf w hnm]; exact houtdeg w
    · exact houtdeg w
    · rw [hpr] at hpa; simp [RuleResult.isApplicable] at hpa
  · rw [if_neg hpa]
    obtain ⟨s, ff, l⟩ := sf
    rcases s with _ | _
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · exact houtdeg w
      · exact houtdeg w
      · exact houtdeg w
      · exact houtdeg w
      · exact houtdeg w
      · -- box φ (boxPos): propagates to existing successors, never mints.
        dsimp only
        split <;> exact houtdeg w
      · -- diamond φ (diamondPos): mints a fresh world (native, genuinely minting).
        dsimp only
        by_cases hw : w = l
        · rw [hw]
          rw [outDeg_addEdge_self,
            filter_minting_append_of_minting_at e ⟨.pos, Proposition.diamond φ, l⟩ (by rfl)]
          simp only [List.length_append, List.length_singleton]
          rw [houtdeg l]
        · rw [outDeg_addEdge_ne acc l (modalNextWorld b) w hw]
          rw [filter_minting_append_of_minting_ne e _ w (by simpa using hw)]
          exact houtdeg w
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · exact houtdeg w
      · exact houtdeg w
      · exact houtdeg w
      · exact houtdeg w
      · exact houtdeg w
      · -- box φ (boxNeg): mints a fresh world.
        dsimp only
        by_cases hw : w = l
        · rw [hw]
          rw [outDeg_addEdge_self,
            filter_minting_append_of_minting_at e ⟨.neg, Proposition.box φ, l⟩ (by rfl)]
          simp only [List.length_append, List.length_singleton]
          rw [houtdeg l]
        · rw [outDeg_addEdge_ne acc l (modalNextWorld b) w hw]
          rw [filter_minting_append_of_minting_ne e _ w (by simpa using hw)]
          exact houtdeg w
      · -- diamond φ (diamondNeg): propagates to existing successors, never mints.
        dsimp only
        split <;> exact houtdeg w

/-- **Generic form**: `modalStepBranchGen apply` preserves the out-degree/
expanded-set correspondence for an abstract `apply : RuleApply Atom`, given its per-call
outDeg-step obligation `hOutDegStep` (the raw hypothesis underlying
`RuleApplicationSpec.outDegStep`, spelled out here rather than bundled, to avoid an import cycle
with `GenericDriver.lean`).
`modalStepBranch_preserves_outDegEq` (K) is the trivial instantiation at
`apply := modalApplyOne`, `hOutDegStep := modalApplyOne_outDeg_step`. -/
lemma modalStepBranch_preserves_outDegEq_gen
    (apply : RuleApply Atom)
    (hOutDegStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length) →
      ∀ w, outDeg (apply sf b acc).snd w =
        (List.filter (fun x => x.label == w && isMintingShaped x)
          (match (apply sf b acc).fst with
            | .linear _ => e ++ [sf]
            | .branching _ => e ++ [sf]
            | .persistent _ => e
            | .notApplicable => (e : List (SignedFormula (Proposition Atom) WorldIndex)))).length)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (houtdeg : ∀ w, outDeg acc w =
      (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ e' ∈ newExps, ∀ w, outDeg newAcc w =
      (e'.filter (fun x => x.label == w && isMintingShaped x)).length := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hcases := hOutDegStep sf b e acc houtdeg
  rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf hcases
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    rw [hsf.2.2] at hcases
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact hcases
  · rw [hfstc] at hsf hcases
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    rw [hsf.2.2] at hcases
    intro e' he'
    rw [← hsf.2.1] at he'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
    exact hcases
  · rw [hfstc] at hsf hcases
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    rw [hsf.2.2] at hcases
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact hcases
  · rw [hfstc] at hsf; simp at hsf

/-- **P2-obl-c** supporting invariant: `modalStepBranch` preserves the out-degree/expanded-set
correspondence `outDeg acc w = |{formulas in e matching isMintingShaped at w}|` for every world
`w`. Zero-regression corollary of `modalStepBranch_preserves_outDegEq_gen` at
`apply := modalApplyOne` via the `modalStepBranch_eq` bridge; statement byte-unchanged. -/
lemma modalStepBranch_preserves_outDegEq
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (houtdeg : ∀ w, outDeg acc w =
      (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ e' ∈ newExps, ∀ w, outDeg newAcc w =
      (e'.filter (fun x => x.label == w && isMintingShaped x)).length := by
  rw [modalStepBranch_eq] at hstep
  exact modalStepBranch_preserves_outDegEq_gen modalApplyOne modalApplyOne_outDeg_step
    b e acc newBs newExps newAcc hstep houtdeg


omit [DecidableEq Atom] in
omit [Hashable Atom] in
/-- Inversion for `isMintingShaped`: a minting-shaped signed formula is either `boxNeg`-shaped
(sign `.neg`, formula a box) or `diamondPos`-shaped (sign `.pos`, formula a diamond; the
native `diamond` constructor genuinely mints). -/
private lemma isMintingShaped_inv
    {sf : SignedFormula (Proposition Atom) WorldIndex} (h : isMintingShaped sf = true) :
    (sf.sign = .neg ∧ ∃ ψ, sf.formula = .box ψ) ∨
      (sf.sign = .pos ∧ ∃ ψ, sf.formula = .diamond ψ) := by
  unfold isMintingShaped at h
  obtain ⟨s, ff, l⟩ := sf
  rcases s with _ | _ <;> rcases ff with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ψ | ψ <;> simp_all

omit [DecidableEq Atom] in
omit [Hashable Atom] in
/-- Bridging fact: filtering then mapping equals a single `filterMap` with the predicate
folded into the `Option`-valued function. Used to invoke `List.Nodup.filterMap`'s
injective-on-domain hypothesis (weaker than `List.Nodup.map`'s global injectivity) for the
`outDeg ≤ Sf` bound below. -/
private lemma filter_map_eq_filterMap
    {β : Type*} (l : List (SignedFormula (Proposition Atom) WorldIndex))
    (p : SignedFormula (Proposition Atom) WorldIndex → Bool)
    (f : SignedFormula (Proposition Atom) WorldIndex → β) :
    (l.filter p).map f = l.filterMap (fun x => if p x then some (f x) else none) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases h : p x = true
    · simp [h, ih]
    · simp [h, ih]

omit [DecidableEq Atom] in
omit [Hashable Atom] in
/-- **P2-obl-c** (final): given `e.Nodup` (P2-obl-a) and the closure fact `e ⊆ modalUniverse φ0`,
`outDeg acc w` is bounded by `Sf(φ0) := (modalSubfmls φ0).length`. The injective map is
`x ↦ x.formula` on `{x ∈ e : x.label = w ∧ isMintingShaped x}`: `isMintingShaped` fixes
`x.sign = .neg` and the shape `.box _`, and the filter fixes `x.label = w`, so `x.formula`
determines `x` uniquely on this set (structure equality) — the injectivity hypothesis of
`List.Nodup.filterMap`. -/
lemma outDeg_le_of_expandedNodup
    (φ0 : Proposition Atom) (e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex)
    (hnodup : e.Nodup) (hclosure : ∀ x ∈ e, x ∈ modalUniverse φ0)
    (houtdeg : outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    outDeg acc w ≤ (modalSubfmls φ0).length := by
  rw [houtdeg, ← List.length_map (fun x => x.formula), filter_map_eq_filterMap]
  have hfmnodup : (e.filterMap (fun x =>
      if x.label == w && isMintingShaped x then some x.formula else none)).Nodup := by
    apply hnodup.filterMap
    intro a a' ψ ha ha'
    simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at ha ha'
    obtain ⟨hacond, haeq⟩ := ha
    obtain ⟨ha'cond, ha'eq⟩ := ha'
    simp only [Bool.and_eq_true] at hacond ha'cond
    obtain ⟨halw, hamint⟩ := hacond
    obtain ⟨ha'lw, ha'mint⟩ := ha'cond
    have hlab : a.label = a'.label :=
      (beq_iff_eq.mp halw).trans (beq_iff_eq.mp ha'lw).symm
    have hform : a.formula = a'.formula := haeq.trans ha'eq.symm
    rcases isMintingShaped_inv hamint with ⟨hasign, ψa, haform⟩ | ⟨hasign, ψa, haform⟩ <;>
      rcases isMintingShaped_inv ha'mint with ⟨ha'sign, ψa', ha'form⟩ | ⟨ha'sign, ψa', ha'form⟩
    · obtain ⟨as, af, al⟩ := a
      obtain ⟨a's, a'f, a'l⟩ := a'
      simp only [] at hasign ha'sign
      simp only [] at hform
      simp only [] at hlab
      subst hasign; subst ha'sign; subst hform; subst hlab
      rfl
    · rw [haform, ha'form] at hform; exact absurd hform (by simp)
    · rw [haform, ha'form] at hform; exact absurd hform (by simp)
    · obtain ⟨as, af, al⟩ := a
      obtain ⟨a's, a'f, a'l⟩ := a'
      simp only [] at hasign ha'sign
      simp only [] at hform
      simp only [] at hlab
      subst hasign; subst ha'sign; subst hform; subst hlab
      rfl
  have hsub : ∀ x ∈ e.filterMap (fun x =>
      if x.label == w && isMintingShaped x then some x.formula else none),
      x ∈ modalSubfmls φ0 := by
    intro ψ hψ
    simp only [List.mem_filterMap] at hψ
    obtain ⟨x, hxmem, hxeq⟩ := hψ
    split at hxeq
    · simp only [Option.some.injEq] at hxeq
      subst hxeq
      exact modalUniverse_mem_formula (hclosure x hxmem)
    · simp at hxeq
  exact (List.subperm_of_subset hfmnodup hsub).length_le


/-! ## Potential Function Φ (obligation d — definitions only)

The scalar potential offsetting `modalMaxWorld`'s growth. The naive per-world term
`(Sf − outDeg acc w) * geomCap Sf (rank w − 1)` is WRONG at a rank-0 ("leaf") world, because
`Nat`'s truncated subtraction silently turns `rank w − 1` into `0` when `rank w = 0`, giving
`geomCap Sf 0 = 1` and a spurious nonzero term `Sf * 1 = Sf` instead of the mathematically
correct `0` (a leaf has no remaining capacity to contribute). This breaks the hand-verified
"exact Δ = 0" step lemma in the `rank = 1`-child (i.e. `rank = 0`) sub-case: hand-tracing the
mint step shows `Δ(maxWorld) + Δ(Φ) = 1 + (Sf − 1) = Sf ≠ 0` with the naive term, vs.
`1 + (−1) = 0` with the corrected piecewise term below. The `rank ≥ 2` sub-case is unaffected
either way (both formulas agree there) and closes via `geomCap_mul_eq_succ_sub_one`. -/

/-- The per-world potential term, corrected for the `rank = 0` (leaf) boundary case: `0` when
`w` has no remaining rank budget (a leaf can mint no further worlds), otherwise
`(Sf − outDeg acc w) * geomCap Sf (rank w − 1)` (remaining successor slots times the capacity
each could still spawn). See the section doc comment for why the `rank = 0` case must be `0`
rather than the naive formula's Nat-truncation artifact. -/
def modalPotentialTerm (Sf : Nat) (acc : Accessibility) (rank : WorldIndex → Nat)
    (w : WorldIndex) : Nat :=
  if rank w = 0 then 0 else (Sf - outDeg acc w) * geomCap Sf (rank w - 1)

/-- The scalar potential `Φ := Σ_{w ∈ modalKnownWorlds b} modalPotentialTerm Sf acc rank w`,
summing over the branch's distinct known world labels (`modalKnownWorlds`, `Branch.lean:87-89`).
-/
def modalPotential (Sf : Nat) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (rank : WorldIndex → Nat) : Nat :=
  ((modalKnownWorlds b).map (modalPotentialTerm Sf acc rank)).sum

/-! ## Known-Worlds and Max-World Bookkeeping (obligation d — finish)

General, `modalStepBranch`-independent facts about `modalKnownWorlds`/`modalMaxWorld` under list
append, needed to show the potential `Φ` is exactly preserved (up to the single fresh-world
term) across a step. -/

omit [DecidableEq Atom] [Hashable Atom] in
lemma modalKnownWorlds_le_modalMaxWorld
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {w : WorldIndex}
    (h : w ∈ modalKnownWorlds b) : w ≤ modalMaxWorld b := by
  rw [mem_modalKnownWorlds] at h
  obtain ⟨sf, hsf, rfl⟩ := h
  exact label_le_modalMaxWorld hsf

omit [DecidableEq Atom] [Hashable Atom] in
private lemma modalNextWorld_not_mem_modalKnownWorlds
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalNextWorld b ∉ modalKnownWorlds b := by
  intro hmem
  have hle := modalKnownWorlds_le_modalMaxWorld hmem
  unfold modalNextWorld at hle
  exact Nat.not_succ_le_self _ hle

omit [DecidableEq Atom] [Hashable Atom] in
private lemma modalKnownWorlds_toFinset_append
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    (modalKnownWorlds (xs ++ b)).toFinset =
      (xs.map SignedFormula.label).toFinset ∪ (modalKnownWorlds b).toFinset := by
  ext x
  simp only [Finset.mem_union, List.mem_toFinset, mem_modalKnownWorlds, List.mem_append,
    List.mem_map]
  constructor
  · rintro ⟨sf, hsf | hsf, rfl⟩
    · exact Or.inl ⟨sf, hsf, rfl⟩
    · exact Or.inr ⟨sf, hsf, rfl⟩
  · rintro (⟨sf, hsf, rfl⟩ | ⟨sf, hsf, rfl⟩)
    · exact ⟨sf, Or.inl hsf, rfl⟩
    · exact ⟨sf, Or.inr hsf, rfl⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- If all labels of `xs` are already known worlds of `b`, appending `xs` doesn't change the
known-worlds set (up to `Perm`). -/
private lemma modalKnownWorlds_perm_append_of_subset
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : ∀ sf ∈ xs, sf.label ∈ modalKnownWorlds b) :
    (modalKnownWorlds (xs ++ b)).Perm (modalKnownWorlds b) := by
  apply List.perm_of_nodup_nodup_toFinset_eq (modalKnownWorlds_nodup _) (modalKnownWorlds_nodup _)
  rw [modalKnownWorlds_toFinset_append]
  have hsub : (xs.map SignedFormula.label).toFinset ⊆ (modalKnownWorlds b).toFinset := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨sf, hsf, rfl⟩ := hx
    simpa using h sf hsf
  exact Finset.union_eq_right.mpr hsub

omit [DecidableEq Atom] [Hashable Atom] in
/-- If `xs` is nonempty and all its labels equal a fresh world `w'` not already known,
appending `xs` prepends `w'` to the known-worlds set (up to `Perm`). -/
private lemma modalKnownWorlds_perm_append_single
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) (w' : WorldIndex)
    (hxsne : xs ≠ []) (hxs : ∀ sf ∈ xs, sf.label = w') (hw' : w' ∉ modalKnownWorlds b) :
    (modalKnownWorlds (xs ++ b)).Perm (w' :: modalKnownWorlds b) := by
  apply List.perm_of_nodup_nodup_toFinset_eq (modalKnownWorlds_nodup _)
    (List.nodup_cons.mpr ⟨hw', modalKnownWorlds_nodup _⟩)
  rw [modalKnownWorlds_toFinset_append]
  have hxseq : (xs.map SignedFormula.label).toFinset = {w'} := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_singleton]
    constructor
    · rintro ⟨sf, hsf, rfl⟩; exact hxs sf hsf
    · intro hxeq
      obtain ⟨sf, hsf⟩ := List.exists_mem_of_ne_nil xs hxsne
      exact ⟨sf, hsf, hxeq ▸ (hxs sf hsf)⟩
  rw [hxseq, List.toFinset_cons, Finset.singleton_union]

omit [DecidableEq Atom] [Hashable Atom] in
/-- Bound on a `max`-fold: if the accumulator and every element's label are `≤ M`, the fold
stays `≤ M`. -/
private lemma modalMaxWorld_foldl_le
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (c M : Nat) (hc : c ≤ M)
    (h : ∀ sf ∈ l, sf.label ≤ M) :
    l.foldl (fun mx sf => max mx sf.label) c ≤ M := by
  induction l generalizing c with
  | nil => simpa using hc
  | cons sf rest ih =>
    simp only [List.foldl_cons]
    exact ih (max c sf.label) (max_le hc (h sf List.mem_cons_self))
      (fun x hx => h x (List.mem_cons_of_mem _ hx))

omit [DecidableEq Atom] [Hashable Atom] in
private lemma modalMaxWorld_le_of_forall_le
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (M : Nat)
    (h : ∀ sf ∈ l, sf.label ≤ M) : modalMaxWorld l ≤ M :=
  modalMaxWorld_foldl_le l 0 M (Nat.zero_le _) h

omit [DecidableEq Atom] [Hashable Atom] in
/-- If every label of `xs` is already `≤ modalMaxWorld b`, appending `xs` doesn't change
`modalMaxWorld`. -/
private lemma modalMaxWorld_append_eq_of_forall_le
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : ∀ sf ∈ xs, sf.label ≤ modalMaxWorld b) :
    modalMaxWorld (xs ++ b) = modalMaxWorld b := by
  apply le_antisymm
  · apply modalMaxWorld_le_of_forall_le
    intro sf hsf
    rcases List.mem_append.mp hsf with hxs | hb
    · exact h sf hxs
    · exact label_le_modalMaxWorld hb
  · exact modalMaxWorld_le_append xs b

omit [DecidableEq Atom] [Hashable Atom] in
/-- If `xs` is nonempty and all its labels equal a fresh world `w'` strictly greater than
`modalMaxWorld b`, appending `xs` sets `modalMaxWorld` to exactly `w'`. -/
private lemma modalMaxWorld_append_single
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) (w' : WorldIndex)
    (hxsne : xs ≠ []) (hxs : ∀ sf ∈ xs, sf.label = w') (hgt : modalMaxWorld b < w') :
    modalMaxWorld (xs ++ b) = w' := by
  apply le_antisymm
  · apply modalMaxWorld_le_of_forall_le
    intro sf hsf
    rcases List.mem_append.mp hsf with hxs' | hb
    · exact le_of_eq (hxs sf hxs')
    · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld hb) hgt)
  · obtain ⟨sf0, hsf0⟩ := List.exists_mem_of_ne_nil xs hxsne
    have := label_le_modalMaxWorld (List.mem_append_left b hsf0)
    rwa [hxs sf0 hsf0] at this

/-! ## `accTargetsKnown` Invariant and the Known-Worlds Dichotomy (obligation d — finish)

`accTargetsKnown b acc` records that every accessibility-edge target is a label already
appearing on the branch. This is needed to lift the `boxPos`/`diamondNeg` closure facts
(`x.label ∈ acc.successorsOf w`) to `x.label ∈ modalKnownWorlds b`, which is what
`modalPotential`'s summation domain tracks. -/

/-- Every accessibility-edge target is a label already appearing on the branch. -/
def accTargetsKnown (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∀ w w', acc.hasEdge w w' → w' ∈ modalKnownWorlds b

/-- **Generic form**: `modalStepBranchGen apply` preserves `accTargetsKnown`,
given the per-call freshness dichotomy `hFreshLocal` (the raw hypothesis underlying
`RuleApplicationSpec.freshLocal`, spelled out here rather than bundled, to avoid the import cycle
with `GenericDriver.lean`). Old edges' targets remain
known since the branch only grows (`modalKnownWorlds_mono_append`); the one possible new edge
targets the freshly-minted witness world, which is immediately present on the new branch.
`modalStepBranch_preserves_accTargetsKnown` (K) is the trivial instantiation at
`apply := modalApplyOne`, `hFreshLocal := modalApplyOne_fresh_local`. -/
lemma modalStepBranch_preserves_accTargetsKnown_gen
    (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hbsub : ∀ b' ∈ newBs, modalKnownWorlds b ⊆ modalKnownWorlds b' := by
    rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact modalKnownWorlds_mono_append nf b
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
      exact modalKnownWorlds_mono_append br b
    · rw [hfstc] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact modalKnownWorlds_mono_append nf b
    · rw [hfstc] at hsf; simp at hsf
  have hnewAcc : newAcc = (apply sf b acc).snd := by
    rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp at hsf
  intro b' hb' w w' hedge
  rw [hnewAcc] at hedge
  rcases hFreshLocal sf b acc with hsame | ⟨wsf, rest, hfst, hsnd⟩
  · rw [hsame] at hedge
    exact hbsub b' hb' (hknown w w' hedge)
  · rw [hsnd] at hedge
    rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
    · have hwsfmem : wsf ∈ b' := by
        rw [hfst] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact List.mem_append_left _ List.mem_cons_self
      rw [mem_modalKnownWorlds]
      exact ⟨wsf, hwsfmem, rfl⟩
    · exact hbsub b' hb' (hknown w w' hold)

/-- **P2-obl-d prerequisite**: `modalStepBranch` preserves `accTargetsKnown`. Zero-regression
corollary of `modalStepBranch_preserves_accTargetsKnown_gen` at
`apply := modalApplyOne` via the `modalStepBranch_eq` bridge; statement byte-unchanged. -/
lemma modalStepBranch_preserves_accTargetsKnown
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc := by
  rw [modalStepBranch_eq] at hstep
  exact modalStepBranch_preserves_accTargetsKnown_gen modalApplyOne modalApplyOne_fresh_local
    b e acc newBs newExps newAcc hstep hknown

omit [Hashable Atom] in
/-- Shared closure fact for the fresh-world-minting groups (`diamondPos`'s live shape and
`boxNeg`'s live shape, `Rules.lean:93-141`; `diamondPos` is native and genuinely
mints): every emitted formula's label is exactly `modalNextWorld b`, since the witness,
`boxProps`, and `diaNegProps` are all constructed at that one fresh label. Parametrized over
the witness's sign/formula so both rule shapes share one proof (mirrors
`boxProps_outputs_subset`/`diaNegProps_outputs_subset`'s factoring). -/
lemma mintGroup_label_eq_freshWorld
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (s0 : Sign) (ψ0 : Proposition Atom) :
    ∀ x ∈ ((⟨s0, ψ0, modalNextWorld b⟩ :
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
          | .diamond ψ =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none)),
    x.label = modalNextWorld b := by
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hbox) | hdia
  · rfl
  · simp only [List.mem_filterMap] at hbox
    obtain ⟨⟨ψ, src⟩, -, heq⟩ := hbox
    split at heq
    · split at heq
      · simp at heq
      · simp only [Option.some.injEq] at heq; subst heq; rfl
    · simp at heq
  · simp only [List.mem_filterMap] at hdia
    obtain ⟨sf', -, heq⟩ := hdia
    split at heq
    · split at heq
      · rename_i ψ hform
        split at heq
        · simp at heq
        · simp only [Option.some.injEq] at heq; subst heq; rfl
      · simp at heq
    · simp at heq

omit [Hashable Atom] in
/-- **Generic per-call knownWorlds-step obligation**: the single-call known-worlds
dichotomy `modalStepBranch_knownWorlds`'s proof needs about `modalApplyOne` at each firing,
extracted as its own lemma so the surrounding driver-unfolding argument (rule-agnostic: it only
inspects the four `RuleResult` constructor shapes) can be replayed for an abstract `apply` given
this fact as a `RuleApplicationSpec` field (`knownWorldsStep`, `GenericDriver.lean`). Either
`apply sf b acc` leaves `acc` unchanged and its output's labels all lie in `modalKnownWorlds b`,
or it mints exactly one edge `sf.label → modalNextWorld b` with a nonempty `.linear` result
entirely labeled at `modalNextWorld b`. -/
lemma modalApplyOne_knownWorlds_step
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    ((modalApplyOne sf b acc).snd = acc ∧
      (match (modalApplyOne sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOne sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOne sf b acc).fst with
        | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
        | .branching _ => False
        | .persistent _ => False
        | .notApplicable => False)) := by
  have hprop := modalApplyOne_prop_outputs_subset sf
  unfold modalApplyOne
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · simp only [hpa, if_true]
    refine Or.inl ⟨trivial, ?_⟩
    rcases hpr : tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
      formulas | branches | formulas | -
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨-, hzlabel⟩ := hprop z hz
      rw [hzlabel, mem_modalKnownWorlds]; exact ⟨sf, hsfmem, rfl⟩
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨-, hzlabel⟩ := hprop z hz
      rw [hzlabel, mem_modalKnownWorlds]; exact ⟨sf, hsfmem, rfl⟩
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨-, hzlabel⟩ := hprop z hz
      rw [hzlabel, mem_modalKnownWorlds]; exact ⟨sf, hsfmem, rfl⟩
    · rw [hpr] at hpa; simp [RuleResult.isApplicable] at hpa
  · rw [if_neg hpa]
    obtain ⟨s, ff, l⟩ := sf
    rcases s with _ | _
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · exact Or.inl ⟨rfl, trivial⟩
      · exact Or.inl ⟨rfl, trivial⟩
      · exact Or.inl ⟨rfl, trivial⟩
      · exact Or.inl ⟨rfl, trivial⟩
      · exact Or.inl ⟨rfl, trivial⟩
      · -- box φ (boxPos): propagates to existing successors.
        dsimp only
        by_cases hemp : (boxPropagation b acc φ l).isEmpty = true
        · simp only [if_pos hemp]; exact Or.inl ⟨trivial, trivial⟩
        · simp only [if_neg hemp]
          refine Or.inl ⟨trivial, ?_⟩
          intro x hx
          obtain ⟨-, hxsucc⟩ := modalApplyOne_boxPos_outputs_subset b acc φ l x hx
          exact hknown l x.label (mem_successorsOf_hasEdge hxsucc)
      · -- diamond φ (diamondPos): mints a fresh world.
        dsimp only
        right
        refine ⟨rfl, List.cons_ne_nil _ _, ?_⟩
        exact fun x hx => mintGroup_label_eq_freshWorld b l Sign.pos φ x hx
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · exact Or.inl ⟨rfl, trivial⟩
      · exact Or.inl ⟨rfl, trivial⟩
      · exact Or.inl ⟨rfl, trivial⟩
      · exact Or.inl ⟨rfl, trivial⟩
      · exact Or.inl ⟨rfl, trivial⟩
      · -- box φ (boxNeg): mints a fresh world.
        dsimp only
        right
        refine ⟨rfl, List.cons_ne_nil _ _, ?_⟩
        exact fun x hx => mintGroup_label_eq_freshWorld b l Sign.neg φ x hx
      · -- diamond φ (diamondNeg): propagates to existing successors.
        dsimp only
        by_cases hemp : ((acc.successorsOf l).filterMap (fun w' =>
            if b.any (· == (⟨.neg, φ, w'⟩ :
                SignedFormula (Proposition Atom) WorldIndex))
            then none
            else some (⟨.neg, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
          ).isEmpty = true
        · simp only [if_pos hemp]; exact Or.inl ⟨trivial, trivial⟩
        · simp only [if_neg hemp]
          refine Or.inl ⟨trivial, ?_⟩
          intro x hx
          obtain ⟨-, hxsucc⟩ := modalApplyOne_diamondNeg_outputs_subset b acc φ l x hx
          exact hknown l x.label (mem_successorsOf_hasEdge hxsucc)

/-- **Generic form**: the known-worlds/max-world dichotomy for a single
`modalStepBranchGen apply` step, given the per-call known-worlds-step obligation
`hKnownWorldsStep` (the raw hypothesis underlying `RuleApplicationSpec.knownWorldsStep`, spelled
out here rather than bundled, to avoid the import cycle with `GenericDriver.lean`). Either `acc`
is unchanged and every child branch's known-worlds/max-world are unchanged (up to `Perm`); or
`acc` gains exactly one edge from some known world `l`
to the fresh world `modalNextWorld b`, and every child branch's known-worlds/max-world gain
exactly that one fresh world. `modalStepBranch_knownWorlds` (K) is the trivial instantiation at
`apply := modalApplyOne`, `hKnownWorldsStep := modalApplyOne_knownWorlds_step`. -/
lemma modalStepBranch_knownWorlds_gen
    (apply : RuleApply Atom)
    (hKnownWorldsStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accTargetsKnown b acc →
      ((apply sf b acc).snd = acc ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
          | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .notApplicable => True)) ∨
      ((apply sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
          | .branching _ => False
          | .persistent _ => False
          | .notApplicable => False)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) :
    (newAcc = acc ∧
      ∀ b' ∈ newBs, modalMaxWorld b' = modalMaxWorld b ∧
        (modalKnownWorlds b').Perm (modalKnownWorlds b)) ∨
    (∃ l ∈ modalKnownWorlds b, newAcc = acc.addEdge l (modalNextWorld b) ∧
      ∀ b' ∈ newBs, modalMaxWorld b' = modalNextWorld b ∧
        (modalKnownWorlds b').Perm (modalNextWorld b :: modalKnownWorlds b)) := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hcases := hKnownWorldsStep sf b acc hsfmem hknown
  have hlknown : sf.label ∈ modalKnownWorlds b := by
    rw [mem_modalKnownWorlds]; exact ⟨sf, hsfmem, rfl⟩
  rcases hcases with ⟨hsame, hmatch⟩ | ⟨haddedge, hfreshall⟩
  · left
    have hnewAcc : newAcc = acc := by
      rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _ <;>
        · rw [hfstc] at hsf
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          first
          | exact hsf.2.2.symm.trans hsame
          | simp at hsf
    refine ⟨hnewAcc, ?_⟩
    rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf hmatch
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact ⟨modalMaxWorld_append_eq_of_forall_le nf b
          (fun x hx => modalKnownWorlds_le_modalMaxWorld (hmatch x hx)),
        modalKnownWorlds_perm_append_of_subset nf b hmatch⟩
    · rw [hfstc] at hsf hmatch
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
      have hbrknown : ∀ x ∈ br, x.label ∈ modalKnownWorlds b :=
        fun x hx => hmatch x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)
      exact ⟨modalMaxWorld_append_eq_of_forall_le br b
          (fun x hx => modalKnownWorlds_le_modalMaxWorld (hbrknown x hx)),
        modalKnownWorlds_perm_append_of_subset br b hbrknown⟩
    · rw [hfstc] at hsf hmatch
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro b' hb'
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact ⟨modalMaxWorld_append_eq_of_forall_le nf b
          (fun x hx => modalKnownWorlds_le_modalMaxWorld (hmatch x hx)),
        modalKnownWorlds_perm_append_of_subset nf b hmatch⟩
    · rw [hfstc] at hsf; simp at hsf
  · right
    refine ⟨sf.label, hlknown, ?_, ?_⟩
    · rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _ <;>
        · rw [hfstc] at hsf
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          first
          | exact hsf.2.2.symm.trans haddedge
          | simp at hsf
    · rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
      · rw [hfstc] at hsf hfreshall
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact ⟨modalMaxWorld_append_single nf b (modalNextWorld b) hfreshall.1 hfreshall.2
            (Nat.lt_succ_self _),
          modalKnownWorlds_perm_append_single nf b (modalNextWorld b) hfreshall.1 hfreshall.2
            (modalNextWorld_not_mem_modalKnownWorlds b)⟩
      · rw [hfstc] at hfreshall; exact hfreshall.elim
      · rw [hfstc] at hfreshall; exact hfreshall.elim
      · rw [hfstc] at hsf; simp at hsf

/-- **P2-obl-d prerequisite**: the known-worlds/max-world dichotomy for a single
`modalStepBranch` step. Zero-regression corollary of `modalStepBranch_knownWorlds_gen`
at `apply := modalApplyOne` via the `modalStepBranch_eq` bridge; statement
byte-unchanged. -/
lemma modalStepBranch_knownWorlds
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) :
    (newAcc = acc ∧
      ∀ b' ∈ newBs, modalMaxWorld b' = modalMaxWorld b ∧
        (modalKnownWorlds b').Perm (modalKnownWorlds b)) ∨
    (∃ l ∈ modalKnownWorlds b, newAcc = acc.addEdge l (modalNextWorld b) ∧
      ∀ b' ∈ newBs, modalMaxWorld b' = modalNextWorld b ∧
        (modalKnownWorlds b').Perm (modalNextWorld b :: modalKnownWorlds b)) := by
  rw [modalStepBranch_eq] at hstep
  exact modalStepBranch_knownWorlds_gen modalApplyOne modalApplyOne_knownWorlds_step
    b e acc newBs newExps newAcc hstep hknown

/-- **Generic form**: the expanded set's `modalUniverse` closure is preserved
across a `modalStepBranchGen apply` step, for **any** `apply : RuleApply Atom` -- this fact needs
no per-call obligation about `apply` at all, since `e'` is either `e` unchanged (persistent
rules) or `e ++ [sf]` (linear/branching rules), and in the latter case `sf ∈ modalUniverse φ0`
follows from `sf ∈ b` and the branch closure `hb`, never from anything `apply` itself produces.
Same shallow (top-level `RuleResult`-constructor-only) case split as P2-obl-a.
`modalStepBranch_eClosure` (K) is the trivial instantiation at `apply := modalApplyOne`. -/
lemma modalStepBranch_eClosure_gen
    (apply : RuleApply Atom)
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverse φ0) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverse φ0 := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfU : sf ∈ modalUniverse φ0 := hb sf hsfmem
  rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfU
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfU
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact heclosure
  · rw [hfstc] at hsf; simp at hsf

/-- The expanded set's `modalUniverse` closure is preserved across a `modalStepBranch` step.
Zero-regression corollary of `modalStepBranch_eClosure_gen` at
`apply := modalApplyOne` via the `modalStepBranch_eq` bridge; statement byte-unchanged. -/
lemma modalStepBranch_eClosure
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverse φ0) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverse φ0 := by
  rw [modalStepBranch_eq] at hstep
  exact modalStepBranch_eClosure_gen modalApplyOne φ0 b e acc newBs newExps newAcc hstep hb
    heclosure

/-- **Reusable invariant bundle** (P2-obl-d/e, threaded onward by P5a across the whole
saturation-loop induction): the branch/expanded-set closure facts, the freshness and
successor-known invariants on `acc`, the out-degree/expanded-set correspondence, and the
rank-map invariants, all together. Bundling these lets P5a carry a single hypothesis through
its induction instead of eight separate ones. -/
structure ModalPotentialInv (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (rank : WorldIndex → Nat) : Prop where
  /-- Every branch formula is a member of the fixed finite universe `U(φ0)`. -/
  bClosure : ∀ x ∈ b, x ∈ modalUniverse φ0
  /-- The expanded set has no duplicate entries (P2-obl-a). -/
  eNodup : e.Nodup
  /-- Every expanded-set formula is a member of `U(φ0)`. -/
  eClosure : ∀ x ∈ e, x ∈ modalUniverse φ0
  /-- All of `acc`'s recorded worlds are `< modalNextWorld b`. -/
  accFresh : accFreshInv b acc
  /-- Every `acc`-edge target is a label already appearing on the branch. -/
  accKnown : accTargetsKnown b acc
  /-- `outDeg` exactly counts the minting-shaped formulas in `e` at each world (P2-obl-c). -/
  outDegEq : ∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length
  /-- The rank map bounds every branch formula's modal depth (P2-obl-b). -/
  rankBound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label
  /-- The rank map decreases by exactly 1 across every recorded accessibility edge (P2-obl-b). -/
  rankEdge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w

/-- **The crux (generic form)**: the exact single-step potential-drop
identity for an abstract `apply : RuleApply Atom`, given its four per-call/aggregate step
obligations `hFreshLocal`/`hRankStep`/`hOutDegStep`/`hKnownWorldsStep` (the raw hypotheses
underlying `RuleApplicationSpec.freshLocal`/`rankStep`/`outDegStep`/`knownWorldsStep`, spelled
out here rather than bundled, to avoid the import cycle with `GenericDriver.lean`).
`modalStepBranchGen apply` preserves `modalMaxWorld b +
modalPotential Sf b acc rank` EXACTLY (`Sf := (modalSubfmls φ0).length`), composing
`modalStepBranch_exists_rank'_gen` for the rank map and `modalStepBranch_knownWorlds_gen` for the
known-worlds/max-world bookkeeping. The fresh-world case's `modalMaxWorld` increment of exactly
`1` is offset by an exact `Φ` decrement of exactly `1`: writing `k := rank' (modalNextWorld b)`
(pinned down exactly via `rank'`'s edge invariant applied to the new edge, composed with its
off-fresh-point agreement with `rank`), the per-world potential term at the mint source `l` drops
by exactly `geomCap Sf k`, which equals the fresh world's own potential term plus `1`
(`geomCap_zero`/`geomCap_succ`, matching the two rank sub-cases `k = 0` and `k = k' + 1`). This
is the **crux confirmation**: no field beyond these four (already established by Phases 1-4) is
needed to replay the EXACT potential-drop identity generically -- the whole argument beyond the
four composed helper calls is pure arithmetic (`geomCap`/`Nat`/`ring`), independent of `apply`.
`modalStepBranch_potential_step` (K) is the trivial instantiation at `apply := modalApplyOne`. -/
lemma modalStepBranch_potential_step_gen
    (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (hRankStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accFreshInv b acc →
      ∀ (rank : WorldIndex → Nat),
      (∀ x ∈ b, modalDepth x.formula ≤ rank x.label) →
      (∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) →
      ∃ rank' : WorldIndex → Nat,
        (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
        (∀ w w', (apply sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .branching branches => ∀ x ∈ branches.flatten, modalDepth x.formula ≤ rank' x.label
          | .persistent formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .notApplicable => True))
    (hOutDegStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length) →
      ∀ w, outDeg (apply sf b acc).snd w =
        (List.filter (fun x => x.label == w && isMintingShaped x)
          (match (apply sf b acc).fst with
            | .linear _ => e ++ [sf]
            | .branching _ => e ++ [sf]
            | .persistent _ => e
            | .notApplicable => (e : List (SignedFormula (Proposition Atom) WorldIndex)))).length)
    (hKnownWorldsStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accTargetsKnown b acc →
      ((apply sf b acc).snd = acc ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
          | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .notApplicable => True)) ∨
      ((apply sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
          | .branching _ => False
          | .persistent _ => False
          | .notApplicable => False)))
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (rank : WorldIndex → Nat)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalPotentialInv φ0 b e acc rank) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ b' ∈ newBs, ∀ x ∈ b', modalDepth x.formula ≤ rank' x.label) ∧
      (∀ w w', newAcc.hasEdge w w' → rank' w' + 1 = rank' w) ∧
      (∀ b' ∈ newBs,
        modalMaxWorld b' + modalPotential (modalSubfmls φ0).length b' newAcc rank' =
          modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank) := by
  obtain ⟨hb, hnodup, heclosure, hInv, hknown, houtdeg, hrankbound, hrankedge⟩ := hinv
  obtain ⟨rank', hragree, hrb', hre'⟩ :=
    modalStepBranch_exists_rank'_gen apply hRankStep b e acc newBs newExps newAcc hstep hInv rank
      hrankbound hrankedge
  refine ⟨rank', hragree, hrb', hre', ?_⟩
  set Sf := (modalSubfmls φ0).length with hSfdef
  have hnextne : ∀ w ∈ modalKnownWorlds b, w ≠ modalNextWorld b := fun w hw heq =>
    modalNextWorld_not_mem_modalKnownWorlds b (heq ▸ hw)
  rcases modalStepBranch_knownWorlds_gen apply hKnownWorldsStep b e acc newBs newExps newAcc
      hstep hknown with
    ⟨hsame, hmax⟩ | ⟨l, hlknown, haddedge, hmax⟩
  · -- non-mint: acc and rank are unchanged on the relevant domain
    intro b' hb'
    obtain ⟨hmw, hperm⟩ := hmax b' hb'
    have hmapeq : (modalKnownWorlds b).map (modalPotentialTerm Sf acc rank') =
        (modalKnownWorlds b).map (modalPotentialTerm Sf acc rank) :=
      List.map_congr_left (fun w hw => by
        unfold modalPotentialTerm; rw [hragree w (hnextne w hw)])
    have hpermterm : modalPotential Sf b' acc rank' = modalPotential Sf b acc rank' := by
      unfold modalPotential; exact (hperm.map (modalPotentialTerm Sf acc rank')).sum_eq
    have hrankeq : modalPotential Sf b acc rank' = modalPotential Sf b acc rank := by
      unfold modalPotential; rw [hmapeq]
    rw [hmw, hsame, hpermterm, hrankeq]
  · -- mint: acc gains one edge l → modalNextWorld b; Φ drops by exactly geomCap Sf k + 1 - ... = 1
    intro b' hb'
    obtain ⟨hmw, hperm⟩ := hmax b' hb'
    have hlne : l ≠ modalNextWorld b := hnextne l hlknown
    have hrankl : rank' l = rank l := hragree l hlne
    have hedgenew : newAcc.hasEdge l (modalNextWorld b) = true := by
      rw [haddedge]; simp [Accessibility.hasEdge, Accessibility.addEdge]
    have hrankw' : rank' (modalNextWorld b) + 1 = rank l := by
      have h1 := hre' l (modalNextWorld b) hedgenew
      rwa [hrankl] at h1
    have houtdeg_l : outDeg newAcc l = outDeg acc l + 1 := by
      rw [haddedge]; exact outDeg_addEdge_self acc l (modalNextWorld b)
    have houtdeg_fresh0 : outDeg acc (modalNextWorld b) = 0 := by
      rcases Nat.eq_zero_or_pos (outDeg acc (modalNextWorld b)) with h0 | hpos
      · exact h0
      · exfalso
        obtain ⟨w1, hw1⟩ := List.exists_mem_of_ne_nil (acc.successorsOf (modalNextWorld b))
          (fun hz => by simp [outDeg, hz] at hpos)
        have hedgeacc : acc.hasEdge (modalNextWorld b) w1 = true := mem_successorsOf_hasEdge hw1
        exact absurd (hInv (modalNextWorld b) w1 hedgeacc).1 (lt_irrefl _)
    have houtdeg_fresh : outDeg newAcc (modalNextWorld b) = 0 := by
      rw [haddedge, outDeg_addEdge_ne acc l (modalNextWorld b) (modalNextWorld b) hlne.symm]
      exact houtdeg_fresh0
    -- bound outDeg acc l < Sf via the post-state e' and P2-obl-c
    have heclosure' := modalStepBranch_eClosure_gen apply φ0 b e acc newBs newExps newAcc hstep hb
      heclosure
    have hnodup' := modalStepBranch_preserves_expandedNodup_gen apply b e acc newBs newExps newAcc
      hstep hnodup
    have houtdegeq' := modalStepBranch_preserves_outDegEq_gen apply hOutDegStep b e acc newBs
      newExps newAcc hstep houtdeg
    have hstepcopy := hstep
    simp only [modalStepBranchGen] at hstepcopy
    obtain ⟨sf, hsfmem, hsf0⟩ := List.exists_of_findSome?_eq_some hstepcopy
    split_ifs at hsf0 with hexp
    have hsfU : sf ∈ modalUniverse φ0 := hb sf hsfmem
    have hnewAccne : newAcc ≠ acc := by
      rw [haddedge]
      intro heq
      have hedges : acc.edges = (l, modalNextWorld b) :: acc.edges :=
        congrArg Accessibility.edges heq.symm
      have hlen := congrArg List.length hedges
      simp only [List.length_cons] at hlen
      omega
    rcases hFreshLocal sf b acc with hsame | ⟨wsf, rest, hfst, hsnd⟩
    · exfalso
      apply hnewAccne
      rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
      · rw [hfstc] at hsf0; simp only [Option.some.injEq, Prod.mk.injEq] at hsf0
        exact hsf0.2.2.symm.trans hsame
      · rw [hfstc] at hsf0; simp only [Option.some.injEq, Prod.mk.injEq] at hsf0
        exact hsf0.2.2.symm.trans hsame
      · rw [hfstc] at hsf0; simp only [Option.some.injEq, Prod.mk.injEq] at hsf0
        exact hsf0.2.2.symm.trans hsame
      · rw [hfstc] at hsf0; simp at hsf0
    · rw [hfst] at hsf0
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf0
      have he'mem : (e ++ [sf]) ∈ newExps := by
        rw [← hsf0.2.1]; exact List.mem_singleton_self _
      have hnodupE' : (e ++ [sf]).Nodup := hnodup' _ he'mem
      have hclosureE' : ∀ x ∈ e ++ [sf], x ∈ modalUniverse φ0 := heclosure' _ he'mem
      have houtdegE'l : outDeg newAcc l =
          ((e ++ [sf]).filter (fun x => x.label == l && isMintingShaped x)).length :=
        houtdegeq' _ he'mem l
      have hSfbound : outDeg newAcc l ≤ Sf :=
        outDeg_le_of_expandedNodup φ0 (e ++ [sf]) newAcc l hnodupE' hclosureE' houtdegE'l
      -- core identity at the mint point: the drop in the term at `l` equals the fresh term
      -- plus exactly 1 (geomCap's recurrence), matching Δ(maxWorld) = 1 exactly.
      have hlz : rank l ≠ 0 := by omega
      have hrank'l : rank' l ≠ 0 := by rw [hrankl]; exact hlz
      have hdSf : outDeg acc l + 1 ≤ Sf := by rw [← houtdeg_l]; exact hSfbound
      have hcore : modalPotentialTerm Sf newAcc rank' (modalNextWorld b) +
          modalPotentialTerm Sf newAcc rank' l + 1 = modalPotentialTerm Sf acc rank l := by
        unfold modalPotentialTerm
        rw [if_neg hrank'l, if_neg hlz, houtdeg_fresh, houtdeg_l, hrankl, Nat.sub_add_eq]
        rcases Nat.eq_zero_or_pos (rank' (modalNextWorld b)) with hk0 | hkpos
        · rw [if_pos hk0]
          have hl1 : rank l = 1 := by omega
          rw [hl1, show (1 : Nat) - 1 = 0 from rfl, geomCap_zero]
          omega
        · have hne0 : rank' (modalNextWorld b) ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
          rw [if_neg hne0]
          obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hne0
          have hrl : rank l - 1 = k' + 1 := by omega
          rw [hrl, hk']
          simp only [Nat.sub_zero, Nat.succ_sub_one]
          rw [geomCap_succ]
          set D := Sf - outDeg acc l - 1 with hDdef
          have hSfeq : Sf - outDeg acc l = D + 1 := by omega
          rw [hSfeq]
          ring
      -- assemble via the erase-decomposition of the sum over modalKnownWorlds b
      have hpe : (modalKnownWorlds b).Perm (l :: (modalKnownWorlds b).erase l) :=
        List.perm_cons_erase hlknown
      have hstep1 : modalPotential Sf b' newAcc rank' =
          modalPotentialTerm Sf newAcc rank' (modalNextWorld b) +
          ((modalKnownWorlds b).map (modalPotentialTerm Sf newAcc rank')).sum := by
        unfold modalPotential
        rw [(hperm.map (modalPotentialTerm Sf newAcc rank')).sum_eq, List.map_cons,
          List.sum_cons]
      have hstep2 : ((modalKnownWorlds b).map (modalPotentialTerm Sf newAcc rank')).sum =
          modalPotentialTerm Sf newAcc rank' l +
          (((modalKnownWorlds b).erase l).map (modalPotentialTerm Sf newAcc rank')).sum := by
        rw [(hpe.map (modalPotentialTerm Sf newAcc rank')).sum_eq, List.map_cons, List.sum_cons]
      have hstep2' : modalPotential Sf b acc rank = modalPotentialTerm Sf acc rank l +
          (((modalKnownWorlds b).erase l).map (modalPotentialTerm Sf acc rank)).sum := by
        unfold modalPotential
        rw [(hpe.map (modalPotentialTerm Sf acc rank)).sum_eq, List.map_cons, List.sum_cons]
      have herase_eq :
          (((modalKnownWorlds b).erase l).map (modalPotentialTerm Sf newAcc rank')).sum =
          (((modalKnownWorlds b).erase l).map (modalPotentialTerm Sf acc rank)).sum := by
        congr 1
        apply List.map_congr_left
        intro w hw
        have hwne_l : w ≠ l :=
          ((modalKnownWorlds_nodup b).mem_erase_iff.mp hw).1
        have hwmem : w ∈ modalKnownWorlds b := List.mem_of_mem_erase hw
        have hwne_fresh : w ≠ modalNextWorld b := hnextne w hwmem
        unfold modalPotentialTerm
        rw [hragree w hwne_fresh, haddedge, outDeg_addEdge_ne acc l (modalNextWorld b) w hwne_l]
      have hw'eq : modalNextWorld b = modalMaxWorld b + 1 := rfl
      rw [hmw, hstep1, hstep2, herase_eq, hstep2', ← hcore, hw'eq]
      ring

/-- **P2-obl-d (finish)**: the exact single-step potential-drop identity. Zero-regression
corollary of `modalStepBranch_potential_step_gen` at `apply := modalApplyOne`
via the `modalStepBranch_eq` bridge; statement byte-unchanged. -/
lemma modalStepBranch_potential_step
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (rank : WorldIndex → Nat)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalPotentialInv φ0 b e acc rank) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ b' ∈ newBs, ∀ x ∈ b', modalDepth x.formula ≤ rank' x.label) ∧
      (∀ w w', newAcc.hasEdge w w' → rank' w' + 1 = rank' w) ∧
      (∀ b' ∈ newBs,
        modalMaxWorld b' + modalPotential (modalSubfmls φ0).length b' newAcc rank' =
          modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank) := by
  rw [modalStepBranch_eq] at hstep
  exact modalStepBranch_potential_step_gen modalApplyOne modalApplyOne_fresh_local
    modalApplyOne_rank_step modalApplyOne_outDeg_step modalApplyOne_knownWorlds_step
    φ0 b e acc newBs newExps newAcc rank hstep hinv

/-! ## World-Count Bound (obligation e — final composition) -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- `Sf(φ0) := (modalSubfmls φ0).length` is always positive: `φ0` is always a member of its own
subformula list via `modalSubfmls_self_mem`. -/
lemma modalSf_pos (φ0 : Proposition Atom) : 1 ≤ (modalSubfmls φ0).length :=
  List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem φ0))

omit [DecidableEq Atom] [Hashable Atom] in
/-- `Sf(φ0) := (modalSubfmls φ0).length` can only equal `1` when `φ0` has no proper structural
subformula distinct from itself, i.e. `φ0` is an atom or `⊥` (`imp`/`box` both strictly grow the
subformula list, since each of their immediate constituents already contributes `≥ 1` via
`modalSubfmls_self_mem`) — both leaf shapes have `modalDepth = 0`. This is the fact
`geomCap_le_pow`'s `hdeg` hypothesis needs. -/
lemma modalSf_one_imp_depth_zero (φ0 : Proposition Atom)
    (h : (modalSubfmls φ0).length = 1) : modalDepth φ0 = 0 := by
  cases φ0 with
  | atom p => rfl
  | bot => rfl
  | imp a c =>
    exfalso
    simp only [modalSubfmls, List.length_cons, List.length_append] at h
    have ha : 1 ≤ (modalSubfmls a).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem a))
    have hc : 1 ≤ (modalSubfmls c).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem c))
    omega
  | and a c =>
    exfalso
    simp only [modalSubfmls, List.length_cons, List.length_append] at h
    have ha : 1 ≤ (modalSubfmls a).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem a))
    have hc : 1 ≤ (modalSubfmls c).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem c))
    omega
  | or a c =>
    exfalso
    simp only [modalSubfmls, List.length_cons, List.length_append] at h
    have ha : 1 ≤ (modalSubfmls a).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem a))
    have hc : 1 ≤ (modalSubfmls c).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem c))
    omega
  | box a =>
    exfalso
    simp only [modalSubfmls, List.length_cons] at h
    have ha : 1 ≤ (modalSubfmls a).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem a))
    omega
  | diamond a =>
    exfalso
    simp only [modalSubfmls, List.length_cons] at h
    have ha : 1 ≤ (modalSubfmls a).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem (modalSubfmls_self_mem a))
    omega

/-- **P2-obl-e (final)**: the a-priori world bound `modalWorldBound φ0` is preserved as a loop
invariant of `modalStepBranch`, given the Φ-bound hypothesis `hPhiBound`
(`Sf := (modalSubfmls φ0).length`) — the hand-verified invariant whose EXACT preservation
(not merely non-increase) is `modalStepBranch_potential_step`'s payload. Chain: `Φ ≥ 0` (`Nat`)
plus the exact Δ=0 identity give `modalMaxWorld b' + 1 ≤ geomCap Sf (modalDepth φ0)`, hence
`modalMaxWorld b' < geomCap Sf (modalDepth φ0) ≤ Sf ^ (modalDepth φ0 + 1)` (`geomCap_le_pow`,
using `Sf ≥ 1` unconditionally and `Sf = 1 → modalDepth φ0 = 0`), `≤ (2 · modalComplexity φ0 +
1) ^ (modalDepth φ0 + 1)` (`modalSubfmls_length_le` + pow monotonicity in the base), `≤
(2 · modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1)` (`modalDepth_le_complexity` + pow
monotonicity in the exponent) `= modalWorldBound φ0`.

A terse `hb + hW` loop-invariant target (assuming only `modalMaxWorld b < modalWorldBound φ0`
survives a step) is FALSE — a
branch can carry a single not-yet-fired minting formula at label `modalWorldBound φ0 − 1`,
satisfying the naive hypothesis, whose firing mints world `modalWorldBound φ0`, breaching the
bound (see the doc-comment preceding `isMintingShaped` for the full counterexample argument).
The invariant that actually survives a step is the `Φ`-bound proved here, carried via the
`ModalPotentialInv` bundle (which P5a threads across the whole saturation-loop induction). -/
lemma modalStepBranch_worldBound_gen
    (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (hRankStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accFreshInv b acc →
      ∀ (rank : WorldIndex → Nat),
      (∀ x ∈ b, modalDepth x.formula ≤ rank x.label) →
      (∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) →
      ∃ rank' : WorldIndex → Nat,
        (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
        (∀ w w', (apply sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .branching branches => ∀ x ∈ branches.flatten, modalDepth x.formula ≤ rank' x.label
          | .persistent formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .notApplicable => True))
    (hOutDegStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length) →
      ∀ w, outDeg (apply sf b acc).snd w =
        (List.filter (fun x => x.label == w && isMintingShaped x)
          (match (apply sf b acc).fst with
            | .linear _ => e ++ [sf]
            | .branching _ => e ++ [sf]
            | .persistent _ => e
            | .notApplicable => (e : List (SignedFormula (Proposition Atom) WorldIndex)))).length)
    (hKnownWorldsStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accTargetsKnown b acc →
      ((apply sf b acc).snd = acc ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
          | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .notApplicable => True)) ∨
      ((apply sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
          | .branching _ => False
          | .persistent _ => False
          | .notApplicable => False)))
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (rank : WorldIndex → Nat)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalPotentialInv φ0 b e acc rank)
    (hPhiBound : modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank + 1 ≤
      geomCap (modalSubfmls φ0).length (modalDepth φ0)) :
    ∀ b' ∈ newBs, modalMaxWorld b' < modalWorldBound φ0 := by
  obtain ⟨rank', -, -, -, hpotential⟩ :=
    modalStepBranch_potential_step_gen apply hFreshLocal hRankStep hOutDegStep hKnownWorldsStep
      φ0 b e acc newBs newExps newAcc rank hstep hinv
  intro b' hb'
  have heq := hpotential b' hb'
  have hcombined : modalMaxWorld b' + modalPotential (modalSubfmls φ0).length b' newAcc rank' + 1
      ≤ geomCap (modalSubfmls φ0).length (modalDepth φ0) := by rw [heq]; exact hPhiBound
  have hle : modalMaxWorld b' + 1 ≤
      modalMaxWorld b' + modalPotential (modalSubfmls φ0).length b' newAcc rank' + 1 :=
    Nat.add_le_add_right (Nat.le_add_right _ _) 1
  have hmwlt : modalMaxWorld b' < geomCap (modalSubfmls φ0).length (modalDepth φ0) :=
    Nat.lt_of_succ_le (le_trans hle hcombined)
  have hSfpos : 1 ≤ (modalSubfmls φ0).length := modalSf_pos φ0
  have hSfdeg : (modalSubfmls φ0).length = 1 → modalDepth φ0 = 0 :=
    modalSf_one_imp_depth_zero φ0
  have hcapbound : geomCap (modalSubfmls φ0).length (modalDepth φ0) ≤
      (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) := geomCap_le_pow hSfpos hSfdeg
  have hSfle : (modalSubfmls φ0).length ≤ 2 * modalComplexity φ0 + 1 :=
    modalSubfmls_length_le φ0
  have hpow1 : (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) ≤
      (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) := Nat.pow_le_pow_left hSfle _
  have hdc : modalDepth φ0 ≤ modalComplexity φ0 := modalDepth_le_complexity φ0
  have hpow2 : (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) ≤
      (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hWB : modalWorldBound φ0 = (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) := rfl
  calc modalMaxWorld b' < geomCap (modalSubfmls φ0).length (modalDepth φ0) := hmwlt
    _ ≤ (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) := hcapbound
    _ ≤ (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) := hpow1
    _ ≤ (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) := hpow2
    _ = modalWorldBound φ0 := hWB.symm

/-- **P2-obl-e (final)**: the a-priori world bound `modalWorldBound φ0` is preserved as a loop
invariant of `modalStepBranch`. Zero-regression corollary of `modalStepBranch_worldBound_gen`
at `apply := modalApplyOne` via the `modalStepBranch_eq` bridge; statement
byte-unchanged. -/
lemma modalStepBranch_worldBound
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (rank : WorldIndex → Nat)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalPotentialInv φ0 b e acc rank)
    (hPhiBound : modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank + 1 ≤
      geomCap (modalSubfmls φ0).length (modalDepth φ0)) :
    ∀ b' ∈ newBs, modalMaxWorld b' < modalWorldBound φ0 := by
  rw [modalStepBranch_eq] at hstep
  exact modalStepBranch_worldBound_gen modalApplyOne modalApplyOne_fresh_local
    modalApplyOne_rank_step modalApplyOne_outDeg_step modalApplyOne_knownWorlds_step
    φ0 b e acc newBs newExps newAcc rank hstep hinv hPhiBound

/-! ## Output-Freshness and Per-Rule R-Drop

This section proves the counting measure `modalWork`/`modalExpMeasure` strictly
decreases on every `some` step of `modalStepBranch`, completing the port of
`classicalExpMeasure_step_lt` (`Classical/Completeness.lean:834`). The combinatorial core is a
`List.countP`-drop lemma (`modalCount_notMem_append_drop`) mirroring
`classicalBranchComplexity_drop` (`:509`) at unit weight (a pure count, not a complexity sum);
composed with a weak monotonicity lemma (`modalCount_notMem_mono`, the branch-growth direction),
it gives the two per-rule-kind drop lemmas `modalWork_drop_linear`/`modalWork_drop_persistent`.
The `.persistent`-producing rules' freshness/nonemptiness fact
(`modalApplyOne_persistent_props`) is proved directly over the `boxPropagation`/
successor-`filterMap` raw expressions (mirroring `modalApplyOne_boxPos_outputs_subset`/
`modalApplyOne_diamondNeg_outputs_subset`'s style), assembled via the same top-level case
dispatch as `modalApplyOne_outputs_subset`, before driving the engine `modalExpMeasure_step_lt`
(port of `:834`). -/

/-- **Combinatorial core** (generic over any `BEq`/`LawfulBEq` type, mirroring
`classicalBranchComplexity_drop`, `Classical/Completeness.lean:509`, at unit weight): appending
`x` (a member of `U`, not yet in `l`) to the exclusion list `l` strictly drops, by at least
one, the count of `U`-members excluded by `l`. Proved by induction on `U`, tracking whether the
head element is `x` itself (drops by exactly one), already excluded by `l` (unaffected by the
extra exclusion), or distinct from `x` and not yet excluded (passes both filters, deferred to
the tail via the induction hypothesis). -/
lemma modalCount_notMem_append_drop
    {α : Type*} [BEq α] [LawfulBEq α]
    (U l : List α) (x : α)
    (hxU : x ∈ U) (hxl : l.any (· == x) = false) :
    U.countP (fun y => !((l ++ [x]).any (· == y))) + 1 ≤
      U.countP (fun y => !(l.any (· == y))) := by
  induction U with
  | nil => simp at hxU
  | cons u us ih =>
    rcases List.mem_cons.mp hxU with rfl | hxU'
    · have h1 : (x :: us).countP (fun y => !(l.any (· == y))) =
          us.countP (fun y => !(l.any (· == y))) + 1 := by
        rw [List.countP_cons]; simp [hxl]
      have h2 : (x :: us).countP (fun y => !((l ++ [x]).any (· == y))) =
          us.countP (fun y => !((l ++ [x]).any (· == y))) := by
        rw [List.countP_cons]; simp [List.any_append]
      have hmono : us.countP (fun y => !((l ++ [x]).any (· == y))) ≤
          us.countP (fun y => !(l.any (· == y))) := by
        have hsub : List.Sublist (us.filter (fun y => !((l ++ [x]).any (· == y))))
            (us.filter (fun y => !(l.any (· == y)))) := by
          apply List.monotone_filter_right
          intro y hy
          simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false,
            Bool.not_or, Bool.and_eq_true] at hy
          exact hy.1
        simpa [List.countP_eq_length_filter] using hsub.length_le
      omega
    · by_cases hlu : l.any (· == u)
      · have h1 : (u :: us).countP (fun y => !(l.any (· == y))) =
            us.countP (fun y => !(l.any (· == y))) := by
          rw [List.countP_cons]; simp [hlu]
        have hlu' : (l ++ [x]).any (· == u) = true := by
          rw [List.any_append, hlu, Bool.true_or]
        have h2 : (u :: us).countP (fun y => !((l ++ [x]).any (· == y))) =
            us.countP (fun y => !((l ++ [x]).any (· == y))) := by
          rw [List.countP_cons, hlu']; simp
        have := ih hxU'
        omega
      · by_cases hux : u == x
        · have hux' : u = x := LawfulBEq.eq_of_beq hux
          subst hux'
          have h1 : (u :: us).countP (fun y => !(l.any (· == y))) =
              us.countP (fun y => !(l.any (· == y))) + 1 := by
            rw [List.countP_cons]; simp [hlu]
          have h2 : (u :: us).countP (fun y => !((l ++ [u]).any (· == y))) =
              us.countP (fun y => !((l ++ [u]).any (· == y))) := by
            rw [List.countP_cons]; simp [List.any_append]
          have hmono : us.countP (fun y => !((l ++ [u]).any (· == y))) ≤
              us.countP (fun y => !(l.any (· == y))) := by
            have hsub : List.Sublist (us.filter (fun y => !((l ++ [u]).any (· == y))))
                (us.filter (fun y => !(l.any (· == y)))) := by
              apply List.monotone_filter_right
              intro y hy
              simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false,
                Bool.not_or, Bool.and_eq_true] at hy
              exact hy.1
            simpa [List.countP_eq_length_filter] using hsub.length_le
          omega
        · simp only [Bool.not_eq_true] at hlu
          have h1 : (u :: us).countP (fun y => !(l.any (· == y))) =
              us.countP (fun y => !(l.any (· == y))) + 1 := by
            rw [List.countP_cons]; simp [hlu]
          have hlux' : (l ++ [x]).any (· == u) = false := by
            rw [List.any_append, hlu, Bool.false_or, List.any_cons, List.any_nil,
              Bool.or_false, beq_eq_false_iff_ne]
            simp only [beq_iff_eq] at hux
            exact fun h => hux h.symm
          have h2 : (u :: us).countP (fun y => !((l ++ [x]).any (· == y))) =
              us.countP (fun y => !((l ++ [x]).any (· == y))) + 1 := by
            rw [List.countP_cons]; simp [hlux']
          have := ih hxU'
          omega

/-- **Weak monotonicity**: growing the exclusion list's underlying membership set (`b ⊆ b'`)
can only decrease (never increase) the count of `U`-members excluded by it. Used for the
`|U \ b|` term, which the linear/branching/persistent rules can only ever help (branch formulas
are only ever prepended, never removed). -/
lemma modalCount_notMem_mono
    {α : Type*} [BEq α] [LawfulBEq α]
    (U b b' : List α)
    (hsub : ∀ z ∈ b, z ∈ b') :
    U.countP (fun y => !(b'.any (· == y))) ≤ U.countP (fun y => !(b.any (· == y))) := by
  have hsubf : List.Sublist (U.filter (fun y => !(b'.any (· == y))))
      (U.filter (fun y => !(b.any (· == y)))) := by
    apply List.monotone_filter_right
    intro y hy
    rw [Bool.not_eq_true'] at hy ⊢
    rw [List.any_eq_false] at hy ⊢
    intro z hz
    exact hy z (hsub z hz)
  simpa [List.countP_eq_length_filter] using hsubf.length_le

omit [Hashable Atom] in
/-- **`R`-drop, linear/branching case**: when the fired formula `sf` is added
to the expanded set (`e' = e ++ [sf]`) and the child branch `b'` weakly extends `b` (every rule
child is `newForms ++ b` for some `newForms`, `Saturation.lean:104-123`), the counting measure
strictly drops by at least one. No `U`-membership of `newForms` is required: growing `b` to `b'`
can only help the `|U \ b|` term (`modalCount_notMem_mono`), and `sf ∈ U`, `sf ∉ e` gives the
exact unit drop in `|U \ e|` (`modalCount_notMem_append_drop`). -/
lemma modalWork_drop_linear
    (U b b' e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hsfU : sf ∈ U) (hsfe : e.any (· == sf) = false) (hsub : ∀ z ∈ b, z ∈ b') :
    modalWork U b' (e ++ [sf]) + 1 ≤ modalWork U b e := by
  unfold modalWork
  have hb := modalCount_notMem_mono U b b' hsub
  have he := modalCount_notMem_append_drop U e sf hsfU hsfe
  omega

omit [Hashable Atom] in
/-- **`R`-drop, persistent case**: when the expanded set is unchanged
(`boxPos`/`diamondNeg`) but the child branch `b'` contains a fresh `U`-member `x0` not on `b`
(guaranteed by `modalApplyOne_persistent_props` below, since persistent rules only ever emit
nonempty output whose formulas are `∉ b`), the counting measure strictly drops by at least one:
the `|U \ e|` term is unchanged, and the `|U \ b|` term strictly drops via the same
`modalCount_notMem_append_drop` core applied to the single witness `x0`. -/
lemma modalWork_drop_persistent
    (U b b' e : List (SignedFormula (Proposition Atom) WorldIndex))
    (x0 : SignedFormula (Proposition Atom) WorldIndex)
    (hx0U : x0 ∈ U) (hx0b : x0 ∉ b) (hx0b' : x0 ∈ b') (hsub : ∀ z ∈ b, z ∈ b') :
    modalWork U b' e + 1 ≤ modalWork U b e := by
  unfold modalWork
  have hstep : ∀ z ∈ b ++ [x0], z ∈ b' := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hsub z hz
    · rwa [List.mem_singleton.mp hz]
  have hmono := modalCount_notMem_mono U (b ++ [x0]) b' hstep
  have hx0notin : b.any (· == x0) = false := by
    rw [Bool.eq_false_iff]
    intro hcon
    obtain ⟨z, hz, heq⟩ := List.any_eq_true.mp hcon
    exact hx0b ((LawfulBEq.eq_of_beq heq) ▸ hz)
  have hdrop := modalCount_notMem_append_drop U b x0 hx0U hx0notin
  omega

/-- Every propositional tableau rule (`Rules.lean`'s `applyPropRule`, the 8 Smullyan rules)
never produces a `.persistent` result: each of the 8 explicit `(rule, sign, connective)` match
arms returns `.linear`, `.branching`, or `.notApplicable` (`PropositionalRules.lean:99-145`),
and the wildcard fallback returns `.notApplicable`. Generic over the formula/label types. -/
private lemma applyPropRule_ne_persistent {F L : Type*}
    (andOf? : F → Option (F × F)) (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F)) (negOf? : F → Option F)
    (sf : SignedFormula F L) (rule : PropTableauRule)
    (nf : List (SignedFormula F L)) :
    applyPropRule andOf? orOf? impOf? negOf? sf rule ≠ .persistent nf := by
  unfold applyPropRule
  obtain ⟨s, φ, l⟩ := sf
  cases rule <;> rcases s with _ | _ <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true] <;>
    first
      | (rcases andOf? φ with _ | ⟨_, _⟩ <;> simp)
      | (rcases orOf? φ with _ | ⟨_, _⟩ <;> simp)
      | (rcases impOf? φ with _ | ⟨_, _⟩ <;> simp)
      | (rcases negOf? φ with _ | _ <;> simp)

/-- `tryAllPropRules` (the first-applicable dispatcher over the 8 propositional rules,
`PropositionalRules.lean:147-155`) never produces `.persistent`, since every candidate result
in its search list is an `applyPropRule` output (`applyPropRule_ne_persistent`) and the
not-found default is `.notApplicable`. -/
private lemma tryAllPropRules_ne_persistent {F L : Type*}
    (andOf? : F → Option (F × F)) (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F)) (negOf? : F → Option F)
    (sf : SignedFormula F L) (nf : List (SignedFormula F L)) :
    tryAllPropRules andOf? orOf? impOf? negOf? sf ≠ .persistent nf := by
  simp only [tryAllPropRules]
  rcases hfind :
      ([PropTableauRule.andPos, .andNeg, .orPos, .orNeg, .impPos, .impNeg, .negPos, .negNeg].map
        (applyPropRule andOf? orOf? impOf? negOf? sf ·)).find? (·.isApplicable) with _ | r
  · rw [hfind]; simp
  · simp only [hfind, Option.getD_some]
    have hmem := List.mem_of_find?_eq_some hfind
    simp only [List.mem_map] at hmem
    obtain ⟨rule, -, hrule⟩ := hmem
    rw [← hrule]
    exact applyPropRule_ne_persistent andOf? orOf? impOf? negOf? sf rule nf

/-- Every propositional tableau rule that produces `.branching` produces exactly two
sub-branches (the 3 branching rules `andNeg`/`orPos`/`impPos`, `PropositionalRules.lean:108-127`,
each construct a 2-element `.branching [_, _]` literal). Generic over the formula/label types. -/
private lemma applyPropRule_branching_length {F L : Type*}
    (andOf? : F → Option (F × F)) (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F)) (negOf? : F → Option F)
    (sf : SignedFormula F L) (rule : PropTableauRule)
    (brs : List (List (SignedFormula F L)))
    (h : applyPropRule andOf? orOf? impOf? negOf? sf rule = .branching brs) :
    brs.length = 2 := by
  unfold applyPropRule at h
  obtain ⟨s, φ, l⟩ := sf
  revert h
  cases rule <;> rcases s with _ | _ <;> simp only [reduceCtorEq, IsEmpty.forall_iff] <;>
    first
      | (rcases andOf? φ with _ | ⟨_, _⟩ <;>
          simp only [reduceCtorEq, IsEmpty.forall_iff, RuleResult.branching.injEq])
      | (rcases orOf? φ with _ | ⟨_, _⟩ <;>
          simp only [reduceCtorEq, IsEmpty.forall_iff, RuleResult.branching.injEq])
      | (rcases impOf? φ with _ | ⟨_, _⟩ <;>
          simp only [reduceCtorEq, IsEmpty.forall_iff, RuleResult.branching.injEq])
      | (rcases negOf? φ with _ | _ <;> simp)
  all_goals (intro h; simp [← h])

/-- `tryAllPropRules`'s branching results always have exactly two sub-branches, since every
candidate is an `applyPropRule` output (`applyPropRule_branching_length`). -/
private lemma tryAllPropRules_branching_length {F L : Type*}
    (andOf? : F → Option (F × F)) (orOf? : F → Option (F × F))
    (impOf? : F → Option (F × F)) (negOf? : F → Option F)
    (sf : SignedFormula F L) (brs : List (List (SignedFormula F L)))
    (h : tryAllPropRules andOf? orOf? impOf? negOf? sf = .branching brs) :
    brs.length = 2 := by
  simp only [tryAllPropRules] at h
  rcases hfind :
      ([PropTableauRule.andPos, .andNeg, .orPos, .orNeg, .impPos, .impNeg, .negPos, .negNeg].map
        (applyPropRule andOf? orOf? impOf? negOf? sf ·)).find? (·.isApplicable) with _ | r
  · rw [hfind] at h; simp at h
  · simp only [hfind, Option.getD_some] at h
    have hmem := List.mem_of_find?_eq_some hfind
    simp only [List.mem_map] at hmem
    obtain ⟨rule, -, hrule⟩ := hmem
    rw [← hrule] at h
    exact applyPropRule_branching_length andOf? orOf? impOf? negOf? sf rule brs h

omit [Hashable Atom] in
/-- Every formula emitted by `boxPropagation` (`Branch.lean:194-199`, the `boxPos` rule's
consequence generator) is fresh: not already on the branch. The `filterMap` guard
`if b.any (· == sf) then none else some sf` excludes anything already present. -/
private lemma boxPropagation_fresh
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ boxPropagation b acc ψ w, x ∉ b := by
  intro x hx
  simp only [boxPropagation, List.mem_filterMap] at hx
  obtain ⟨w', -, hxeq⟩ := hx
  by_cases hcond :
      b.any (· == (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
  · rw [if_pos hcond] at hxeq
    simp at hxeq
  · rw [if_neg hcond] at hxeq
    simp only [Option.some.injEq] at hxeq
    subst hxeq
    intro hxb
    simp only [Bool.not_eq_true] at hcond
    rw [List.any_eq_false] at hcond
    exact hcond _ hxb (by simp)

omit [Hashable Atom] in
/-- Every formula emitted by the `diamondNeg` rule's successor-propagation `filterMap`
(`Rules.lean:144-147`, the raw expression underlying `modalApplyOne_diamondNeg_outputs_subset`)
is fresh: not already on the branch, by the same `filterMap` guard. -/
private lemma diamondNeg_filterMap_fresh
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ (acc.successorsOf w).filterMap (fun w' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf') then none else some sf'), x ∉ b := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨w', -, hxeq⟩ := hx
  by_cases hcond :
      b.any (· == (⟨.neg, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
  · rw [if_pos hcond] at hxeq
    simp at hxeq
  · rw [if_neg hcond] at hxeq
    simp only [Option.some.injEq] at hxeq
    subst hxeq
    intro hxb
    simp only [Bool.not_eq_true] at hcond
    rw [List.any_eq_false] at hcond
    exact hcond _ hxb (by simp)

omit [Hashable Atom] in
/-- **Persistent-rule nonemptiness and freshness**: whenever
`modalApplyOne sf b acc` produces a `.persistent` result, the emitted formulas `nf` are both
nonempty (the `isEmpty` guard in `boxPos`/`diamondNeg`, `Rules.lean:83-88,142-151`, routes the
empty case to `.notApplicable` instead) and fresh (`∀ x ∈ nf, x ∉ b`, by the underlying
`filterMap` guards). These are the only two rule kinds that can produce `.persistent`:
propositional rules cannot (`tryAllPropRules_ne_persistent`), and the two fresh-world rules
`diamondPos`/`boxNeg` are `.linear`, dismissed by contradiction with `hca`. Mirrors
`modalApplyOne_outputs_subset`'s case-dispatch skeleton. -/
lemma modalApplyOne_persistent_props
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOne sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  unfold modalApplyOne at hca
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · exfalso
    simp only [hpa, if_true] at hca
    exact tryAllPropRules_ne_persistent modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf nf hca
  · rw [if_neg hpa] at hca
    obtain ⟨s, ff, l⟩ := sf
    rcases s with _ | _
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · simp at hca
      · simp at hca
      · simp at hca
      · simp at hca
      · simp at hca
      · -- box φ (boxPos): persistent.
        dsimp only at hca
        by_cases hemp : (boxPropagation b acc φ l).isEmpty = true
        · simp only [if_pos hemp] at hca; simp at hca
        · simp only [if_neg hemp] at hca
          simp only [RuleResult.persistent.injEq] at hca
          subst hca
          refine ⟨?_, boxPropagation_fresh b acc φ l⟩
          simp only [Bool.not_eq_true] at hemp
          exact List.isEmpty_eq_false_iff.mp hemp
      · -- diamond φ (diamondPos): linear, not persistent -- contradiction.
        dsimp only at hca; simp at hca
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · simp at hca
      · simp at hca
      · simp at hca
      · simp at hca
      · simp at hca
      · -- box φ (boxNeg): linear, not persistent -- contradiction.
        dsimp only at hca; simp at hca
      · -- diamond φ (diamondNeg): persistent.
        dsimp only at hca
        by_cases hemp : ((acc.successorsOf l).filterMap (fun w' =>
            if b.any (· == (⟨.neg, φ, w'⟩ :
                SignedFormula (Proposition Atom) WorldIndex))
            then none
            else some (⟨.neg, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
          ).isEmpty = true
        · simp only [if_pos hemp] at hca; simp at hca
        · simp only [if_neg hemp] at hca
          simp only [RuleResult.persistent.injEq] at hca
          subst hca
          refine ⟨?_, diamondNeg_filterMap_fresh b acc φ l⟩
          simp only [Bool.not_eq_true] at hemp
          exact List.isEmpty_eq_false_iff.mp hemp

omit [Hashable Atom] in
/-- Whenever `modalApplyOne sf b acc` produces a `.branching` result, the result has exactly
two sub-branches. The only rule kind that can produce `.branching` is the propositional
dispatch (`tryAllPropRules_branching_length`); the four modal rules (`boxPos`/`diamondPos`/
`boxNeg`/`diamondNeg`) are `.persistent`/`.linear`, dismissed by contradiction with `hca`.
Mirrors `modalApplyOne_persistent_props`'s case-dispatch skeleton. -/
lemma modalApplyOne_branching_length
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOne sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  unfold modalApplyOne at hca
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · simp only [hpa, if_true] at hca
    exact tryAllPropRules_branching_length modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf brs
      hca
  · rw [if_neg hpa] at hca
    obtain ⟨s, ff, l⟩ := sf
    rcases s with _ | _
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · simp at hca
      · simp at hca
      · simp at hca
      · simp at hca
      · simp at hca
      · dsimp only at hca
        by_cases hemp : (boxPropagation b acc φ l).isEmpty = true
        · simp only [if_pos hemp] at hca; simp at hca
        · simp only [if_neg hemp] at hca; simp at hca
      · dsimp only at hca; simp at hca
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · simp at hca
      · simp at hca
      · simp at hca
      · simp at hca
      · simp at hca
      · dsimp only at hca; simp at hca
      · dsimp only at hca
        by_cases hemp : ((acc.successorsOf l).filterMap (fun w' =>
            if b.any (· == (⟨.neg, φ, w'⟩ :
                SignedFormula (Proposition Atom) WorldIndex))
            then none
            else some (⟨.neg, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
          ).isEmpty = true
        · simp only [if_pos hemp] at hca; simp at hca
        · simp only [if_neg hemp] at hca; simp at hca

/-! ## Strict-Decrease Engine -/

omit [Hashable Atom] in
/-- `classicalExpMeasure_split`-style additivity (`Classical/Completeness.lean:641`), adapted
to `modalExpMeasure`/`modalWork`: the measure splits over a single distinguished position,
given length-aligned prefixes. -/
lemma modalExpMeasure_split
    (U : List (SignedFormula (Proposition Atom) WorldIndex))
    (done : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (rest : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (restEs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hlen : done.length = doneExp.length) :
    modalExpMeasure U (done ++ bh :: rest) (doneExp ++ e :: restEs)
      = modalExpMeasure U done doneExp + 3 ^ modalWork U bh e
        + modalExpMeasure U rest restEs := by
  simp only [modalExpMeasure, List.zip_append hlen, List.zip_cons_cons,
             List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  omega

omit [Hashable Atom] in
/-- `classicalExpMeasure_append`-style additivity (`:656`), adapted to `modalExpMeasure`. -/
lemma modalExpMeasure_append
    (U : List (SignedFormula (Proposition Atom) WorldIndex))
    (l1 l2 : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (e1 e2 : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (h : l1.length = e1.length) :
    modalExpMeasure U (l1 ++ l2) (e1 ++ e2)
      = modalExpMeasure U l1 e1 + modalExpMeasure U l2 e2 := by
  simp only [modalExpMeasure, List.zip_append h, List.map_append, List.sum_append]

omit [Hashable Atom] in
/-- `classicalExpMeasure_const_exp`-style identity (`:666`), adapted to `modalExpMeasure`: when
every new branch shares the same expanded set `newExp`, the measure is the sum of
`3 ^ modalWork U child newExp` over the new branches. -/
lemma modalExpMeasure_const_exp
    (U : List (SignedFormula (Proposition Atom) WorldIndex))
    (newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalExpMeasure U newBs (newBs.map (fun _ => newExp))
      = (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum := by
  simp only [modalExpMeasure, ← List.map_prod_left_eq_zip, List.map_map, Function.comp_def]

/-- **The engine (generic form)**: one `modalStepBranchGen apply` step
strictly decreases the base-3 damped worklist measure by at least one, given the
branch-closure/freshness/world-bound hypotheses `hb`/`hInv`/`hW` and the three per-call/aggregate
obligations `hBranchingLength`/`hPersistentFresh`/`hOutputsSubsetUniverse`. `hBranchingLength` is
an additional raw hypothesis: the `.branching` case needs `apply`'s
branching output to always have exactly two sub-branches, a fact not covered by the other
`RuleApplicationSpec` fields above -- mirrors the `RuleApplicationSpec.branchingLength` field
(`GenericDriver.lean`), discharged for `modalApplyOne` by the pre-existing
`modalApplyOne_branching_length`. `hPersistentFresh`/`hOutputsSubsetUniverse` are the raw forms
of the pre-existing `persistentFresh`/`outputsSubsetUniverse` fields; `hOutputsSubsetUniverse` is
stated at the lemma's own (already-bound) `φ0` rather than universally quantified, so a caller
whose only witness is `RuleApplicationSpecAt`/`RuleApplicationSpecCoreAt` (`GenericDriver.lean`
-- e.g. D, `DDriver.lean`, whose `outputsSubsetUniverse` genuinely fails at an arbitrary `φ0`)
can still discharge it directly, with no `φ0`-specialization needed at the call site. Case-splits
over the four `RuleResult` outcomes exactly as the classical template, replacing
`classicalBranchComplexity`'s per-output complexity accounting with the counting `R`-drop lemmas
(`modalWork_drop_linear`/`_persistent`, already rule-agnostic), whose `+1 ≤` shape supplies both
the `1 ≤ R`-parent bound and the `child ≤ R-1` bound the `pow3_*` lemmas need in one step.
`modalExpMeasure_step_lt` (K) is the trivial instantiation at `apply := modalApplyOne`. -/
lemma modalExpMeasure_step_lt_gen
    (apply : RuleApply Atom)
    (hBranchingLength : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (brs : List (List (SignedFormula (Proposition Atom) WorldIndex))),
      (apply sf b acc).fst = .branching brs → brs.length = 2)
    (hPersistentFresh : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (nf : List (SignedFormula (Proposition Atom) WorldIndex)),
      (apply sf b acc).fst = .persistent nf → nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b)
    (φ0 : Proposition Atom)
    (hOutputsSubsetUniverse : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (∀ x ∈ b, x ∈ modalUniverse φ0) → sf ∈ b → accFreshInv b acc →
      modalMaxWorld b < modalWorldBound φ0 →
      (match (apply sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
        | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverse φ0
        | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
        | .notApplicable => True))
    (done bt newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc newAcc : Accessibility)
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ modalUniverse φ0)
    (hInv : accFreshInv bh acc)
    (hW : modalMaxWorld bh < modalWorldBound φ0)
    (hstep : modalStepBranchGen apply bh e acc = some (newBs, newBs.map (fun _ => newExp),
      newAcc)) :
    modalExpMeasure (modalUniverse φ0) (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ modalExpMeasure (modalUniverse φ0) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  set U := modalUniverse φ0 with hUdef
  have hrhs : modalExpMeasure U (done ++ bh :: bt) (doneExp ++ e :: es) =
      modalExpMeasure U done doneExp + 3 ^ modalWork U bh e + modalExpMeasure U bt es :=
    modalExpMeasure_split U done doneExp bh e bt es hdlen
  have hlhs : modalExpMeasure U (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) =
      modalExpMeasure U done doneExp +
        (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum +
        modalExpMeasure U bt es := by
    have hlen1 : (done ++ newBs).length = (doneExp ++ newBs.map (fun _ => newExp)).length := by
      simp [List.length_append, hdlen]
    rw [modalExpMeasure_append U (done ++ newBs) bt
          (doneExp ++ newBs.map (fun _ => newExp)) es hlen1,
        modalExpMeasure_append U done newBs doneExp (newBs.map (fun _ => newExp)) hdlen,
        modalExpMeasure_const_exp U newBs newExp]
  rw [hrhs, hlhs]
  suffices h : (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum + 1 ≤
      3 ^ modalWork U bh e by omega
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hfound⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hfound with hany
  simp only [Bool.not_eq_true] at hany
  have hsfU : sf ∈ U := hb sf hsfmem
  rcases hca : (apply sf bh acc).1 with nf | brs | nf | -
  · -- linear
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    have hdrop : modalWork U (nf ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (nf ++ bh) e sf hsfU hany (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (nf ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · -- branching
    have hlen2 : brs.length = 2 := hBranchingLength sf bh acc brs hca
    obtain ⟨b0, b1, hbrs⟩ : ∃ b0 b1, brs = [b0, b1] := by
      match brs, hlen2 with
      | [b0, b1], _ => exact ⟨b0, b1, rfl⟩
    subst hbrs
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hdrop0 : modalWork U (b0 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b0 ++ bh) e sf hsfU hany (fun z hz => List.mem_append_right b0 hz)
    have hdrop1 : modalWork U (b1 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b1 ++ bh) e sf hsfU hany (fun z hz => List.mem_append_right b1 hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (b0 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    have h1 : modalWork U (b1 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    exact pow3_two_add_one_le hC h0 h1
  · -- persistent
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    obtain ⟨hnfne, hnffresh⟩ := hPersistentFresh sf bh acc nf hca
    obtain ⟨x0, hx0mem⟩ := List.exists_mem_of_ne_nil nf hnfne
    have hclosure := hOutputsSubsetUniverse sf bh acc hb hsfmem hInv hW
    rw [hca] at hclosure
    have hx0U : x0 ∈ U := hclosure x0 hx0mem
    have hx0b : x0 ∉ bh := hnffresh x0 hx0mem
    have hx0b' : x0 ∈ nf ++ bh := List.mem_append_left bh hx0mem
    have hdrop : modalWork U (nf ++ bh) newExp + 1 ≤ modalWork U bh newExp :=
      modalWork_drop_persistent U bh (nf ++ bh) newExp x0 hx0U hx0b hx0b'
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh newExp := by omega
    have h0 : modalWork U (nf ++ bh) newExp ≤ modalWork U bh newExp - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · rw [hca] at hfound; simp at hfound

/-- **The strict-decrease engine** (port of `classicalExpMeasure_step_lt`,
`Classical/Completeness.lean:834`): one `modalStepBranch` step strictly decreases the base-3
damped worklist measure by at least one. Zero-regression corollary of
`modalExpMeasure_step_lt_gen` at `apply := modalApplyOne` via the
`modalStepBranch_eq` bridge; statement byte-unchanged. -/
lemma modalExpMeasure_step_lt
    (φ0 : Proposition Atom)
    (done bt newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc newAcc : Accessibility)
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ modalUniverse φ0)
    (hInv : accFreshInv bh acc)
    (hW : modalMaxWorld bh < modalWorldBound φ0)
    (hstep : modalStepBranch bh e acc = some (newBs, newBs.map (fun _ => newExp), newAcc)) :
    modalExpMeasure (modalUniverse φ0) (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ modalExpMeasure (modalUniverse φ0) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  rw [modalStepBranch_eq] at hstep
  exact modalExpMeasure_step_lt_gen modalApplyOne modalApplyOne_branching_length
    modalApplyOne_persistent_props φ0 (modalApplyOne_outputs_subset φ0)
    done bt newBs doneExp es newExp bh e acc newAcc hdlen hb hInv hW hstep

/-! ## Downstream Reuse Helpers (T, S5, B existing-world propagation)

The two facts below are public (unlike the closely-related private helpers
`mem_modalUniverse_of'`/`mem_modalKnownWorlds` they are built from) because they are exactly
what a "persistent-only" frame extension (T, S5, B) needs to discharge
`RuleApplicationSpec.outputsSubsetUniverse`/`.knownWorldsStep` for a rule that propagates a
subformula at an existing world (its own world, for T's self propagation; a related world for
S5 and B), rather than minting a fresh one. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Same-world subformula membership: given `sf ∈ b` with `b ⊆ modalUniverse φ0`, any
subformula `ψ` of `sf.formula`, at `sf`'s own world label and with an arbitrary sign, stays
inside `modalUniverse φ0`. -/
lemma modalUniverse_mem_of_sameWorld_subfml {φ0 : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    {sf : SignedFormula (Proposition Atom) WorldIndex} (hsf : sf ∈ b)
    {ψ : Proposition Atom} (hψ : ψ ∈ modalSubfmls sf.formula) (s : Sign) :
    (⟨s, ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverse φ0 := by
  have hlabel : sf.label ≤ modalWorldBound φ0 := modalUniverse_mem_label (hb sf hsf)
  have hform : sf.formula ∈ modalSubfmls φ0 := modalUniverse_mem_formula (hb sf hsf)
  exact mem_modalUniverse_of' hlabel (modalSubfmls_trans hψ hform)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Membership in `modalKnownWorlds`: the label of any branch member is a known world of that
branch. -/
lemma label_mem_modalKnownWorlds
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {sf : SignedFormula (Proposition Atom) WorldIndex} (hsf : sf ∈ b) :
    sf.label ∈ modalKnownWorlds b := (mem_modalKnownWorlds b sf.label).mpr ⟨sf, hsf, rfl⟩

end Cslib.Logic.Modal.Tableau

end
