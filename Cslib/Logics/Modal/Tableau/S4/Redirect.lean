/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.S4.Universe
public import Cslib.Logics.Modal.Tableau.S4.BirthKey
public import Cslib.Logics.Modal.Tableau.S4.Guard
public import Cslib.Logics.Modal.Tableau.S4.Driver
public import Cslib.Logics.Modal.Tableau.S4.Hintikka

/-! # S4 Loop-Checking: Blocked-Redirect and `accWithReds` Machinery

The subtractive-blocking redirect machinery (`Reds`, `accWithReds`) that materializes recorded
redirect decisions as a genuine `Accessibility`, the free-transfer bridges
(`blockedRedirect_{unwrapped,boxed}_{boxPos,diaNeg}_mem`) that let box-positive/diamond-negative
facts propagate across a redirect edge, and the saturation-preservation capstone
`modalS4Saturated_addEdge_of_blocked`.

## Why a separate module

This module sits above `Driver` and `Hintikka` (both below) because
`modalS4Saturated_addEdge_of_blocked` -- despite its `modalS4Saturated` name prefix suggesting
`Hintikka` -- consumes `blockedRedirect_boxed_*`, `successorsOf_addEdge_*`, and
`modalApplyOneS4_*_fst_eq`, all declared earlier in this same file. Research correction 4 of 4:
a reader guessing by name alone would misplace this declaration in `Hintikka`, reintroducing a
forward edge (`Hintikka` would need to import `Redirect`, which already imports `Hintikka`).

## Main Definitions
- `Reds`: a recorded blocking decision list, threaded alongside `keys`.
- `accWithReds`: `acc` augmented with every recorded redirect edge, materialized as a genuine
  `Accessibility`.

## Main Results
- `hasEdge_accWithReds_iff`: `accWithReds` edge-membership characterization.
- `reflTransGen_accWithReds_first_red`: the first-redirect-edge decomposition of a
  `ReflTransGen` path over `accWithReds`.
- `blockedRedirect_unwrapped_boxPos_mem`, `_diaNeg_mem`, `blockedRedirect_boxed_boxPos_mem`,
  `_diaNeg_mem`: the free-transfer bridges across a redirect edge.
- `successorsOf_addEdge_of_ne`, `_self`: `Accessibility.successorsOf` behavior under `addEdge`.
- `modalApplyOneS4_boxPos_fst_eq`, `_diaNeg_fst_eq`, `modalApplyOne_fst_eq_of_not_boxPos_diaNeg`,
  `modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg`, `_fst_congr_successorsOf`: `acc`-independence
  facts for `modalApplyOneS4`'s non-minting output.
- `modalS4Saturated_addEdge_of_blocked`: the capstone -- `modalS4Saturated` preservation under
  the specific `addEdge src wBlock` the keyed minting guard's block performs.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- A recorded blocking decision under subtractive blocking: `(source, blockTarget, sign,
witnessFormula)`. Threaded alongside `keys`, read only by the completeness direction. Matches
the probe's working type
(`specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4subtractive3.lean:43`).
-/
@[nolint unusedArguments]
abbrev Reds (Atom : Type*) [DecidableEq Atom] [Hashable Atom] :=
  List (WorldIndex × WorldIndex × Sign × Proposition Atom)

/-- `acc` augmented with every recorded redirect edge from `red`, materialized as a genuine
`Accessibility`. Since `Accessibility` is a bare edge list (`Branch.lean:55-57`), this lets
`extractModelS4` and its five lemmas (`FrameCompleteness.lean:143-189`) be reused verbatim at
`accWithReds acc red` -- no `extractModelS4Sub` is needed. -/
def accWithReds (acc : Accessibility) (red : Reds Atom) : Accessibility :=
  ⟨acc.edges ++ red.map (fun r => (r.1, r.2.1))⟩

/-- Bridge: `accWithReds acc red` has an edge `x → y` iff `acc` already has it, or some recorded
redirect in `red` targets `y` from `x`. -/
theorem hasEdge_accWithReds_iff (acc : Accessibility) (red : Reds Atom) (x y : WorldIndex) :
    (accWithReds acc red).hasEdge x y =
      (acc.hasEdge x y || red.any (fun r => r.1 == x && r.2.1 == y)) := by
  simp only [accWithReds, Accessibility.hasEdge, List.any_append, List.any_map,
    Function.comp_def]

/-! ## Path Decomposition over `accWithReds`

Retained per the post-Gate-B triage as a general fact about the `Reds`/`accWithReds` packaging
above; independent of the now-dead bifurcated Hintikka predicate that originally motivated it
(`plans/04_subtractive-blocking-red-channel.md`). -/

/-- **Path decomposition** for `ReflTransGen (accWithReds acc red)`: a path `w ⤳ u` either stays
entirely inside `acc.hasEdge`, or its first `red`-hop can be isolated -- it decomposes as an
`acc`-only prefix `w ⤳ x`, a recorded redirect `(x, wB, s, φ) ∈ red`, and a residual
`ReflTransGen (accWithReds acc red)`-suffix `wB ⤳ u`. Proved by
`Relation.ReflTransGen.head_induction_on` plus `hasEdge_accWithReds_iff`: the `head` case's own
edge splits (via the bridge) into an `acc`-edge or a `red`-edge; a `red`-edge terminates the
prefix immediately (the residual is exactly the induction's own tail path, no recursion needed),
while an `acc`-edge prepends onto whichever disjunct the inductive hypothesis already produced. -/
lemma reflTransGen_accWithReds_first_red (acc : Accessibility) (red : Reds Atom)
    (w u : WorldIndex)
    (hpath : Relation.ReflTransGen (fun x y => (accWithReds acc red).hasEdge x y = true) w u) :
    Relation.ReflTransGen (fun x y => acc.hasEdge x y = true) w u ∨
    ∃ (x wB : WorldIndex) (s : Sign) (φ : Proposition Atom),
      Relation.ReflTransGen (fun x y => acc.hasEdge x y = true) w x ∧
      (x, wB, s, φ) ∈ red ∧
      Relation.ReflTransGen (fun x y => (accWithReds acc red).hasEdge x y = true) wB u := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | head hedge htail ih =>
    rename_i w' x
    rw [hasEdge_accWithReds_iff] at hedge
    simp only [Bool.or_eq_true] at hedge
    rcases hedge with hacc | hred
    · rcases ih with hleft | ⟨x', wB, s, φ, hpre, hmemred, hsuf⟩
      · exact Or.inl (Relation.ReflTransGen.head hacc hleft)
      · exact Or.inr ⟨x', wB, s, φ, Relation.ReflTransGen.head hacc hpre, hmemred, hsuf⟩
    · obtain ⟨r, hr_mem, hr_eq⟩ := List.any_eq_true.mp hred
      obtain ⟨rw', rx, rs, rphi⟩ := r
      simp only [Bool.and_eq_true, beq_iff_eq] at hr_eq
      obtain ⟨hrw_eq, hrx_eq⟩ := hr_eq
      rw [hrw_eq, hrx_eq] at hr_mem
      exact Or.inr ⟨w', x, rs, rphi, Relation.ReflTransGen.refl, hr_mem, htail⟩

/-! ## Redirect Forward-Cone Free Transfer (Route-Independent Remnant)

Route (3)'s Decision Gate B (`plans/04_subtractive-blocking-red-channel.md`)
refuted the cone-extension lemma that would have let the two free transfers below
propagate beyond the redirect target `wBlock` itself. The two boxed bridge variants
`hintikkaS4_box_pos_reflTransGen_boxed`/`hintikkaS4_dia_neg_reflTransGen_boxed`, and the
forward-cone conjuncts they fed (`S4KeyedSubHintikkaInv.redBoxForwardCone`/`redDiaForwardCone`),
were deleted from the repository in the post-Gate-B triage by commit `c4b33f63` ("revert
red-channel machinery orphaned by Gate B, retain route-independent assets"). **They no longer
exist**: the only remaining occurrences of all four identifiers anywhere under `Cslib/` are the
two prose mentions in this paragraph, so nothing below may be read as depending on them.

Consequence for the bridge count: the `hintikkaS4_*` bridge set in this file is now **8**
declarations, not the ten that existed when this paragraph was first written (the figure of ten
was correct then; `c4b33f63` removed two of them).

```
grep -nE '^(private )?(theorem|lemma) hintikkaS4_' \
  Cslib/Logics/Modal/Tableau/LoopChecking.lean | wc -l
```

Beware a near-miss measurement: counting *distinct identifiers* over the same file returns 11,
because three further `hintikkaS4_*` names occur only in call positions or prose. The declared
bridge set is 8.

The two lemmas below are the surviving reflexive-case fragment: sorry-free,
standard-axioms-only, true statements about the guard, kept because they are genuinely
route-independent and may be reused by the route (1) successor plan. -/

omit [Hashable Atom] in
/-- **Free transfer, box-context half (condition (c))**: near-transcription of
`modalStepBranchS4Keyed_blocked_witness_mem`'s proof. When a minting attempt at `src` is
blocked to `wBlock`, every box-positive formula `T(□χ)@src` already on the branch (with `χ`
`φ₀`-relevant) transfers, UNWRAPPED, to `wBlock`: `T(χ)@wBlock ∈ b`. This is the reflexive
(`u = wBlock`) base case of a forward-cone obligation that does **not** extend to `u` strictly
beyond `wBlock` in the cone (Decision Gate B refuted that extension; see the module doc above).
**Measured 0 failures / 24,314** (condition (c), `specs/553_.../artifacts/s4subtractive3.lean`). -/
lemma blockedRedirect_unwrapped_boxPos_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock)
    (χ : Proposition Atom) (hsf : (Sign.pos, χ) ∈ signedSubfmls φ₀)
    (hmem : (⟨.pos, .box χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, χ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ src wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ src) hkey
  have hmemSet : (Sign.pos, χ) ∈ successorBirthContent φ₀ b s φ src := by
    unfold successorBirthContent
    refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter]
    refine ⟨hsf, Or.inl ⟨rfl, ?_⟩⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, hmem, rfl⟩
  have hrel := hsub hmemSet
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

omit [Hashable Atom] in
/-- **Free transfer, diamond-context half (condition (e))**: dual of
`blockedRedirect_unwrapped_boxPos_mem`. When a minting attempt at `src` is blocked to `wBlock`,
every diamond-negative formula `F(◇χ)@src` already on the branch (with `χ` `φ₀`-relevant)
transfers, UNWRAPPED, to `wBlock`: `F(χ)@wBlock ∈ b`. **Measured 0 failures / 24,314**
(condition (e)). -/
lemma blockedRedirect_unwrapped_diaNeg_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock)
    (χ : Proposition Atom) (hsf : (Sign.neg, χ) ∈ signedSubfmls φ₀)
    (hmem : (⟨.neg, .diamond χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, χ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ src wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ src) hkey
  have hmemSet : (Sign.neg, χ) ∈ successorBirthContent φ₀ b s φ src := by
    unfold successorBirthContent
    refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter]
    refine ⟨hsf, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, hmem, rfl⟩
  have hrel := hsub hmemSet
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

omit [Hashable Atom] in
/-- **Free transfer, BOXED box-context half -- the box-plus payoff.** Dual of
`blockedRedirect_unwrapped_boxPos_mem`, using the box-plus filter arm instead of the unwrapped
one: when a minting attempt at `src` is blocked to `wBlock`, every box-positive formula
`T(□χ)@src` already on the branch (with `□χ` itself `φ₀`-relevant) transfers in its own BOXED
form to `wBlock`: `T(□χ)@wBlock ∈ b`, not merely the unwrapped `T(χ)@wBlock ∈ b` the unenriched
key could only ever give. This is the box-plus enrichment's payoff: `successorBirthContent`'s
third disjunct records `(pos, □χ)` directly, so `keyLowerBd` lower-bounds it into
`relevantSetFinset`'s BOXED slot at `wBlock`, giving the boxed membership as a three-line
consequence -- exactly the "Redirect-Inertness Assembly -- REMOVED" section's recommended
repair route, landed. -/
lemma blockedRedirect_boxed_boxPos_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock)
    (χ : Proposition Atom) (hsf : (Sign.pos, .box χ) ∈ signedSubfmls φ₀)
    (hmem : (⟨.pos, .box χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, .box χ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ src wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ src) hkey
  have hmemSet : (Sign.pos, .box χ) ∈ successorBirthContent φ₀ b s φ src := by
    unfold successorBirthContent
    refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter]
    refine ⟨hsf, Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, hmem, rfl⟩
  have hrel := hsub hmemSet
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

omit [Hashable Atom] in
/-- **Free transfer, BOXED diamond-context half -- the box-plus payoff.** Dual of
`blockedRedirect_boxed_boxPos_mem`, using the box-plus filter's fourth disjunct: when a minting
attempt at `src` is blocked to `wBlock`, every diamond-negative formula `F(◇χ)@src` already on
the branch (with `◇χ` itself `φ₀`-relevant) transfers in its own BOXED (diamond) form to
`wBlock`: `F(◇χ)@wBlock ∈ b`. -/
lemma blockedRedirect_boxed_diaNeg_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock)
    (χ : Proposition Atom) (hsf : (Sign.neg, .diamond χ) ∈ signedSubfmls φ₀)
    (hmem : (⟨.neg, .diamond χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, .diamond χ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ src wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ src) hkey
  have hmemSet : (Sign.neg, .diamond χ) ∈ successorBirthContent φ₀ b s φ src := by
    unfold successorBirthContent
    refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter]
    refine ⟨hsf, Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, hmem, rfl⟩
  have hrel := hsub hmemSet
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

/-! ## Saturation Preservation Under the Keyed Redirect (Plan v6, re-scoped Phases 3-5)

Per the `#### Phase 1 Verdict` in `plans/07_canonical-witness-truth-lemma.md`
(`specs/553_s4_loop_guard_soundness_reachability_restriction/`), the sole remaining obligation
for the redirect-preservation argument is `modalS4Saturated` preservation under the specific
`addEdge src wBlock` a keyed-guard block performs. `modalApplyOneS4`'s output at a signed formula
`sf` depends on `acc` ONLY through `acc.successorsOf sf.label` (`blockingWorldS4`, the K rules,
the T self-propagation arms, and the 4-rule arms are all either acc-independent or route through
`successorsOf sf.label` alone), so the two `successorsOf`/`addEdge` lemmas below make that
dependence explicit at the two points this obligation needs: invariance when `sf.label ≠ src`,
and the extended-successor content when `sf.label = src`. -/

omit [Hashable Atom] in
/-- `Accessibility.successorsOf` is unaffected by `addEdge` at any world other than the
redirect's source: the new edge only ever extends `src`'s own successor list. -/
lemma successorsOf_addEdge_of_ne (acc : Accessibility) (src wBlock v : WorldIndex)
    (hne : v ≠ src) : (acc.addEdge src wBlock).successorsOf v = acc.successorsOf v := by
  unfold Accessibility.successorsOf Accessibility.addEdge
  simp only [List.filterMap_cons, beq_iff_eq]
  rw [if_neg (Ne.symm hne)]

omit [Hashable Atom] in
/-- `Accessibility.successorsOf` at the redirect's source, after `addEdge`, is `wBlock`
prepended to the original successor list. -/
lemma successorsOf_addEdge_self (acc : Accessibility) (src wBlock : WorldIndex) :
    (acc.addEdge src wBlock).successorsOf src = wBlock :: acc.successorsOf src := by
  unfold Accessibility.successorsOf Accessibility.addEdge
  simp

/-- Closed form for `modalApplyOneS4`'s `.fst` at the box-positive shape `T(□ψ)@w`: the T-rule
(`modalTBoxSelf`) and 4-rule (`modalFourBoxProp`) propagation arms' merge on top of K's
`boxPropagation`, spelled out explicitly rather than left behind a `let`. Reusable scaffolding
for both `modalApplyOneS4_fst_congr_successorsOf` and `modalS4Saturated_addEdge_of_blocked`:
both need to compare this expression at two different accessibilities, and it is far easier to
compare the closed form (which isolates every acc-dependent subterm as `boxPropagation`/
`modalFourBoxProp` applied to that accessibility) than to re-derive it twice. -/
lemma modalApplyOneS4_boxPos_fst_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4 φ₀ (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
    (match (match (if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
              else RuleResult.persistent (boxPropagation b acc ψ w)) with
          | RuleResult.persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | RuleResult.notApplicable =>
            if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTBoxSelf b ψ w)
          | other => other) with
      | RuleResult.persistent tForms =>
        RuleResult.persistent
          (tForms ++ (modalFourBoxProp b acc ψ w).filter (fun x => !(tForms.any (· == x))))
      | RuleResult.notApplicable =>
        if (modalFourBoxProp b acc ψ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (modalFourBoxProp b acc ψ w)
      | other => other) := by
  have hk : (modalApplyOne (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
      else RuleResult.persistent (boxPropagation b acc ψ w) := by
    unfold modalApplyOne
    simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
      modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
    split_ifs <;> simp_all
  have htR : (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOne (⟨.pos, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | RuleResult.persistent kForms =>
          RuleResult.persistent
            (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
        | RuleResult.notApplicable =>
          if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalTBoxSelf b ψ w)
        | other => other) := by
    unfold modalApplyOneT
    obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases kResult <;> first | rfl | (simp only []; split <;> rfl)
  have htS4 : (modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | RuleResult.persistent tForms =>
          RuleResult.persistent
            (tForms ++ (modalFourBoxProp b acc ψ w).filter (fun x => !(tForms.any (· == x))))
        | RuleResult.notApplicable =>
          if (modalFourBoxProp b acc ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalFourBoxProp b acc ψ w)
        | other => other) := by
    unfold modalApplyOneS4Rules
    obtain ⟨tResult, tAcc⟩ := modalApplyOneT (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases tResult <;> first | rfl | (simp only []; split <;> rfl)
  have hshape : modalApplyOneS4 φ₀ (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc =
      modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape, htS4, htR, hk]
  rfl

/-- Dual of `modalApplyOneS4_boxPos_fst_eq` for the diamond-negative shape `F(◇ψ)@w`, via
`modalTDiaNegSelf`/`modalFourDiaNegProp` and the inline diamond-negative K rule arm (there is no
separately named `def` for the K layer here, unlike `boxPropagation`, so its filterMap is
spelled out directly). -/
lemma modalApplyOneS4_diaNeg_fst_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4 φ₀ (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
    (match (match (if ((acc.successorsOf w).filterMap fun u =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
              if b.any (· == sf') then none else some sf').isEmpty then
            RuleResult.notApplicable
          else
            RuleResult.persistent ((acc.successorsOf w).filterMap fun u =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
              if b.any (· == sf') then none else some sf')) with
          | RuleResult.persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | RuleResult.notApplicable =>
            if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTDiaNegSelf b ψ w)
          | other => other) with
      | RuleResult.persistent tForms =>
        RuleResult.persistent
          (tForms ++ (modalFourDiaNegProp b acc ψ w).filter (fun x => !(tForms.any (· == x))))
      | RuleResult.notApplicable =>
        if (modalFourDiaNegProp b acc ψ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (modalFourDiaNegProp b acc ψ w)
      | other => other) := by
  have hk : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      if ((acc.successorsOf w).filterMap fun u =>
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
            if b.any (· == sf') then none else some sf').isEmpty then
        RuleResult.notApplicable
      else
        RuleResult.persistent ((acc.successorsOf w).filterMap fun u =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
          if b.any (· == sf') then none else some sf') := by
    unfold modalApplyOne
    simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
      modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
    split_ifs <;> simp_all
  have htR : (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | RuleResult.persistent kForms =>
          RuleResult.persistent
            (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
        | RuleResult.notApplicable =>
          if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalTDiaNegSelf b ψ w)
        | other => other) := by
    unfold modalApplyOneT
    obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases kResult <;> first | rfl | (simp only []; split <;> rfl)
  have htS4 : (modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | RuleResult.persistent tForms =>
          RuleResult.persistent
            (tForms ++ (modalFourDiaNegProp b acc ψ w).filter (fun x => !(tForms.any (· == x))))
        | RuleResult.notApplicable =>
          if (modalFourDiaNegProp b acc ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalFourDiaNegProp b acc ψ w)
        | other => other) := by
    unfold modalApplyOneS4Rules
    obtain ⟨tResult, tAcc⟩ := modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases tResult <;> first | rfl | (simp only []; split <;> rfl)
  have hshape : modalApplyOneS4 φ₀ (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc =
      modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape, htS4, htR, hk]
  rfl

omit [Hashable Atom] in
/-- `modalApplyOne`'s (the underlying K-rule dispatch, no S4 guard) `.fst` component is
**entirely independent of `acc`** outside its own two acc-consulting shapes (`T(□φ)@w`, whose
`boxPropagation` reads `acc.successorsOf w`, and `F(◇φ)@w`, whose inline dual does the same):
the propositional rules and both minting arms (`F(□φ)`, `T(◇φ)`) never consult `acc` for their
`.fst` content, only for the accessibility they hand back as `.snd`. -/
lemma modalApplyOne_fst_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc1 acc2 : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∧
         ¬ (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)) :
    (modalApplyOne sf b acc1).fst = (modalApplyOne sf b acc2).fst := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOne
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp_all [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?,
      List.map, List.find?, RuleResult.isApplicable, Option.getD_none] <;>
    split_ifs <;> rfl

/-- `modalApplyOneS4`'s `.fst` component is **entirely independent of `acc`** outside the two
4-rule/T-rule-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`): the guard's own minting/blocking decision
(`blockingWorldS4`) never consults `acc`, and every other rule arm (K's mint rules, the
propositional rules, the T self-propagation arms) is likewise acc-free at these shapes.
Companion to `modalApplyOneS4_eq_of_not_boxNeg_diaPos` (which handles the *guard*-relevant
shapes `F(□φ)`/`T(◇φ)`), but for the complementary shape set and for the `.fst` projection
against two arbitrary accessibilities rather than one fixed reduction target. -/
lemma modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc1 acc2 : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∧
         ¬ (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)) :
    (modalApplyOneS4 φ₀ sf b acc1).fst = (modalApplyOneS4 φ₀ sf b acc2).fst := by
  obtain ⟨h1, h2⟩ := h
  by_cases hg1 : sf.sign = .neg ∧ ∃ ψ, sf.formula = .box ψ
  · obtain ⟨hs, ψ, hf⟩ := hg1
    have hsfeq : sf = (⟨.neg, .box ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
      rcases sf with ⟨s', f', w'⟩; simp_all
    rw [hsfeq]
    rcases hblk : blockingWorldS4 φ₀ b .neg ψ sf.label with _ | wBlock
    · rw [modalApplyOneS4_boxNeg_unblocked_eq φ₀ b acc1 ψ sf.label hblk,
        modalApplyOneS4_boxNeg_unblocked_eq φ₀ b acc2 ψ sf.label hblk]
      exact modalApplyOne_fst_eq_of_not_boxPos_diaNeg _ b acc1 acc2 ⟨by simp, by simp⟩
    · rw [modalApplyOneS4_boxNeg_blocked_eq φ₀ b acc1 ψ sf.label wBlock hblk,
        modalApplyOneS4_boxNeg_blocked_eq φ₀ b acc2 ψ sf.label wBlock hblk]
  · by_cases hg2 : sf.sign = .pos ∧ ∃ ψ, sf.formula = .diamond ψ
    · obtain ⟨hs, ψ, hf⟩ := hg2
      have hsfeq : sf = (⟨.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq]
      rcases hblk : blockingWorldS4 φ₀ b .pos ψ sf.label with _ | wBlock
      · rw [modalApplyOneS4_diaPos_unblocked_eq φ₀ b acc1 ψ sf.label hblk,
          modalApplyOneS4_diaPos_unblocked_eq φ₀ b acc2 ψ sf.label hblk]
        exact modalApplyOne_fst_eq_of_not_boxPos_diaNeg _ b acc1 acc2 ⟨by simp, by simp⟩
      · rw [modalApplyOneS4_diaPos_blocked_eq φ₀ b acc1 ψ sf.label wBlock hblk,
          modalApplyOneS4_diaPos_blocked_eq φ₀ b acc2 ψ sf.label wBlock hblk]
    · -- Neither guard shape (`F(□φ)`, `T(◇φ)`) nor either 4-rule shape (`T(□φ)`, `F(◇φ)`):
      -- `modalApplyOneS4` reduces all the way to `modalApplyOne`, whose `.fst` at the five
      -- remaining (non-modal) shapes never mentions `acc` at all.
      have hshape1 : modalApplyOneS4 φ₀ sf b acc1 = modalApplyOneS4Rules sf b acc1 :=
        modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc1 ⟨hg1, hg2⟩
      have hshape2 : modalApplyOneS4 φ₀ sf b acc2 = modalApplyOneS4Rules sf b acc2 :=
        modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc2 ⟨hg1, hg2⟩
      rw [hshape1, hshape2, modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc1 ⟨h1, h2⟩,
        modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc2 ⟨h1, h2⟩,
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc1 ⟨h1, h2⟩,
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc2 ⟨h1, h2⟩]
      exact modalApplyOne_fst_eq_of_not_boxPos_diaNeg sf b acc1 acc2 ⟨h1, h2⟩

/-- `modalApplyOneS4`'s `.fst` component depends on `acc` ONLY through `acc.successorsOf
sf.label`: whenever two accessibilities agree there, the whole rule output agrees. Companion to
`modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg`, covering the two shapes that lemma excludes
(`T(□φ)@w`, `F(◇φ)@w`) via `modalApplyOneS4_boxPos_fst_eq`/`_diaNeg_fst_eq`'s closed forms,
whose only `acc`-dependent subterms (`boxPropagation`/`modalFourBoxProp`/the inline
diamond-negative filterMap/`modalFourDiaNegProp`) all route through `acc.successorsOf sf.label`
alone and so rewrite directly under `hsucc`. -/
lemma modalApplyOneS4_fst_congr_successorsOf (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc1 acc2 : Accessibility)
    (hsucc : acc1.successorsOf sf.label = acc2.successorsOf sf.label) :
    (modalApplyOneS4 φ₀ sf b acc1).fst = (modalApplyOneS4 φ₀ sf b acc2).fst := by
  by_cases hhard :
      (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∨
      (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)
  · rcases hhard with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨.pos, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq, modalApplyOneS4_boxPos_fst_eq φ₀ b acc1 ψ sf.label,
        modalApplyOneS4_boxPos_fst_eq φ₀ b acc2 ψ sf.label]
      unfold boxPropagation modalFourBoxProp
      rw [hsucc]
    · have hsfeq : sf = (⟨.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq, modalApplyOneS4_diaNeg_fst_eq φ₀ b acc1 ψ sf.label,
        modalApplyOneS4_diaNeg_fst_eq φ₀ b acc2 ψ sf.label]
      unfold modalFourDiaNegProp
      rw [hsucc]
  · exact modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg φ₀ sf b acc1 acc2 (not_or.mp hhard)

/-- **The hard content** (re-scoped Phase 3's remaining obligation, per the plan's
`#### Phase 3 Progress Record`): `modalS4Saturated` preservation under the specific `addEdge
src wBlock` the keyed minting guard's block performs. Combines `modalApplyOneS4_fst_congr_
successorsOf`/`modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg` (acc-dependence is confined to
`acc.successorsOf sf.label`, and only at the two 4-rule-relevant shapes) with the box-plus free
transfers `blockedRedirect_boxed_boxPos_mem`/`_diaNeg_mem` and the landed T-self bridges
`hintikkaS4_box_pos_self`/`hintikkaS4_dia_neg_self` (recovering the UNWRAPPED fact at `wBlock`
from the BOXED one, at the *original*, unextended `acc`, since the T self-propagation arm never
consults `acc` at all). Once both the boxed and unwrapped facts land at `wBlock`, the extended
accessibility's box-positive/diamond-negative persistent output at `src` is LITERALLY the same
list as the original's (the new `wBlock` entry in `acc.successorsOf src` is filtered out of
every propagation arm by those two facts), so the extended-acc saturation goal reduces exactly
to `hSat` applied at the unextended `acc`. -/
lemma modalS4Saturated_addEdge_of_blocked (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hSat : modalS4Saturated φ₀ b acc)
    (hUniv : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock) :
    modalS4Saturated φ₀ b (acc.addEdge src wBlock) := by
  intro sf hsfmem
  have hcond := hSat sf hsfmem
  by_cases hhard :
      (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∨
      (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)
  · by_cases hlabel : sf.label = src
    · -- The hard case: `sf` sits at the redirect's source and is one of the two
      -- 4-rule-relevant shapes. Establish literal `.fst` equality via the two free-transfer
      -- facts, then reduce to `hcond`.
      have hfst : (modalApplyOneS4 φ₀ sf b (acc.addEdge src wBlock)).fst =
          (modalApplyOneS4 φ₀ sf b acc).fst := by
        rcases hhard with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
        · -- box-positive at src: T(□ψ)@src ∈ b
          have hmemBox : (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
              b := by
            have : sf = (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
              rcases sf with ⟨s', f', w'⟩
              simp_all
            rwa [this] at hsfmem
          have hsigsub : (Sign.pos, .box ψ) ∈ signedSubfmls φ₀ :=
            mem_signedSubfmls_of_formula_s4loop .pos (modalUniverseS4_mem_formula (hUniv _ hmemBox))
          have hboxedWB : (⟨.pos, .box ψ, wBlock⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            blockedRedirect_boxed_boxPos_mem φ₀ b keys s φ src wBlock hkL hblock ψ hsigsub hmemBox
          have hunwrappedWB : (⟨.pos, ψ, wBlock⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hintikkaS4_box_pos_self φ₀ b acc hSat ψ wBlock hboxedWB
          have hsfeq : sf = (⟨.pos, .box ψ, src⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := by
            rcases sf with ⟨s', f', w'⟩; simp_all
          have hAddEq : boxPropagation b (acc.addEdge src wBlock) ψ src =
              boxPropagation b acc ψ src := by
            unfold boxPropagation
            rw [successorsOf_addEdge_self, List.filterMap_cons]
            have hin : (b.any fun x => x ==
                (⟨.pos, ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true := by
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨_, hunwrappedWB, rfl⟩
            simp [hin]
          have hFourEq : modalFourBoxProp b (acc.addEdge src wBlock) ψ src =
              modalFourBoxProp b acc ψ src := by
            unfold modalFourBoxProp
            rw [successorsOf_addEdge_self, List.filterMap_cons]
            have hin : (b.any fun x => x ==
                (⟨.pos, .box ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true := by
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨_, hboxedWB, rfl⟩
            simp [hin]
          rw [hsfeq, modalApplyOneS4_boxPos_fst_eq φ₀ b (acc.addEdge src wBlock) ψ src,
            modalApplyOneS4_boxPos_fst_eq φ₀ b acc ψ src, hAddEq, hFourEq]
        · -- diamond-negative at src: F(◇ψ)@src ∈ b
          have hmemDia : (⟨.neg, .diamond ψ, src⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
            have : sf = (⟨.neg, .diamond ψ, src⟩ :
                SignedFormula (Proposition Atom) WorldIndex) := by
              rcases sf with ⟨s', f', w'⟩
              simp_all
            rwa [this] at hsfmem
          have hsigsub : (Sign.neg, .diamond ψ) ∈ signedSubfmls φ₀ :=
            mem_signedSubfmls_of_formula_s4loop .neg
              (modalUniverseS4_mem_formula (hUniv _ hmemDia))
          have hboxedWB : (⟨.neg, .diamond ψ, wBlock⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            blockedRedirect_boxed_diaNeg_mem φ₀ b keys s φ src wBlock hkL hblock ψ hsigsub
              hmemDia
          have hunwrappedWB : (⟨.neg, ψ, wBlock⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hintikkaS4_dia_neg_self φ₀ b acc hSat ψ wBlock hboxedWB
          have hsfeq : sf = (⟨.neg, .diamond ψ, src⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := by
            rcases sf with ⟨s', f', w'⟩; simp_all
          have hAddEq : ((acc.addEdge src wBlock).successorsOf src).filterMap
              (fun u => let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
                if b.any (· == sf') then none else some sf') =
              (acc.successorsOf src).filterMap
              (fun u => let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
                if b.any (· == sf') then none else some sf') := by
            rw [successorsOf_addEdge_self, List.filterMap_cons]
            have hin : (b.any fun x => x ==
                (⟨.neg, ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true := by
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨_, hunwrappedWB, rfl⟩
            simp [hin]
          have hFourEq : modalFourDiaNegProp b (acc.addEdge src wBlock) ψ src =
              modalFourDiaNegProp b acc ψ src := by
            unfold modalFourDiaNegProp
            rw [successorsOf_addEdge_self, List.filterMap_cons]
            have hin : (b.any fun x => x ==
                (⟨.neg, .diamond ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex)) =
                true := by
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨_, hboxedWB, rfl⟩
            simp [hin]
          rw [hsfeq, modalApplyOneS4_diaNeg_fst_eq φ₀ b (acc.addEdge src wBlock) ψ src,
            modalApplyOneS4_diaNeg_fst_eq φ₀ b acc ψ src, hAddEq, hFourEq]
      simpa only [hfst] using hcond
    · -- `sf.label ≠ src`: acc-dependence is confined to `acc.successorsOf sf.label`, invariant.
      have hsucc := successorsOf_addEdge_of_ne acc src wBlock sf.label hlabel
      have hfst := modalApplyOneS4_fst_congr_successorsOf φ₀ sf b (acc.addEdge src wBlock) acc
        hsucc
      simpa only [hfst] using hcond
  · -- Not one of the two 4-rule-relevant shapes: `.fst` is acc-independent absolutely.
    have hfst := modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg φ₀ sf b (acc.addEdge src wBlock) acc
      (not_or.mp hhard)
    simpa only [hfst] using hcond

end Cslib.Logic.Modal.Tableau

end
