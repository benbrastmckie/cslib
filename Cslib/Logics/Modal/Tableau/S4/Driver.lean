/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Dedup
public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.S4.Universe
public import Cslib.Logics.Modal.Tableau.S4.BirthKey
public import Cslib.Logics.Modal.Tableau.S4.Guard
public import Cslib.Logics.Modal.Tableau.Support.Accessibility
public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds

/-! # S4 Loop-Checking: Rule-Application Driver (Definitions and Equation Lemmas)

The S4 rule-application and step-branch **definitions** (`modalApplyOneS4`,
`modalStepBranchS4`, `modalExpandBranchesS4`, `modalTableauS4`, the keyed-minting and
keyed-driver family `modalApplyOneS4KeyedMint`/`modalApplyOneS4Keyed`/
`modalStepBranchS4Keyed{,Body,Ordered}`) and their immediate equation, shape, and witness
lemmas. This is the structurally forced seventh module (research option A, a recorded
deviation from the task description's six-family list): the invariant material below makes
~248 references into these definitions, so leaving them in `LoopChecking.lean` would create an
import cycle between the invariant modules and the barrel.

## Why a separate module

Every declaration here is consumed, directly or transitively, by material that must sit above
it (`Hintikka`, `Redirect`, the four invariant modules) -- keeping it in `LoopChecking.lean`
would force those modules to import the barrel, which imports them, a cycle. This module (plus
its Phase 6 continuation) is deliberately the single largest module in the cluster: it is the
one place a reader needs the whole rule-application surface in one file to follow how
`modalApplyOneS4Keyed`'s case split threads through `modalStepBranchS4Keyed` to
`modalStepBranchS4KeyedOrdered`.

**Split across two phases at a verified-acyclic seam.** This file holds the *definitions* and
their immediate equation/shape/witness lemmas (49 declarations); `S4/Driver.lean`'s Phase 6
continuation adds the remaining composite lemmas (known-worlds and universe-membership
facts, `branch_superset`, the `RuleApplySt` bridge, etc.). The two halves were verified
reference-acyclic (zero forward edges from this half into the Phase 6 half) before the split.

## Main Definitions
- `modalApplyOneS4`, `modalStepBranchS4`, `modalExpandBranchesS4`, `modalTableauS4`: the
  unkeyed S4 rule-application and driver family.
- `modalApplyOneS4KeyedMint`, `modalApplyOneS4Keyed`: the keyed minting guard and rule
  application.
- `modalNonMintCandidates`: the non-minting candidate sublist (settled-context scheduling).
- `modalStepBranchS4Keyed`, `modalStepBranchS4KeyedBody`, `modalStepBranchS4KeyedOrdered`: the
  keyed step-branch family, culminating in the ordered stepper.

## Main Results
- The `modalApplyOneS4{,Keyed}_*_{blocked,unblocked}_eq` equation-lemma groups.
- `modalApplyOneS4KeyedMint_snd_eq`, `_fst_eq_or_linear`: keyed-mint shape facts.
- `modalNonMintCandidates_subset`, `_not_mem_expanded`, `_eq_nil_iff`: non-mint candidate
  characterization.
- `modalStepBranchS4KeyedOrdered_cases`, `_eq_none_iff`, `_selected_mem`, `_mintReady`: the
  ordered stepper's case analysis.
- The `modalApplyOneS4Rules_*_fst` / `_eq_S4Rules` and `modalApplyOne_*_mint_*_S4` groups, and
  the `modalApplyOneS4KeyedMint_*_eq_S4` / `_witness` group: minting-payload equations.
- `boxProps_outputs_subset_S4`, `diaNegProps_outputs_subset_S4`,
  `modalApplyOne_{diamondPos,boxNeg}_outputs_subset_S4`: the universe-membership output bounds
  for the fresh-world minting rules.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- The `φ₀`-parameterized S4 rule-application function (Decision D1). Wraps
`modalApplyOneS4Rules` (K + T + 4, `FrameRules.lean`). At the two **minting** shapes
(`F(□φ)@w`, `T(◇φ)@w` -- the shapes where the underlying K rule would create a fresh
world), consults `blockingWorldS4` (fixes Gap 2, the guard now compares the
*prospective successor's* birth content, not the source world `w`'s own set):
- **blocked** (`some wBlock`): returns `.linear []` and `acc.addEdge w wBlock` -- a
  loop-back edge to the existing blocking world, minting **no** new world.
- **unblocked** (`none`): falls through unchanged to `modalApplyOneS4Rules` (hence to the
  underlying rule's fresh-world minting, `modalApplyOneS4_unblocked_eq` below).

This is the one place S4 departs structurally from K: everywhere else, `modalApplyOneS4`
is exactly `modalApplyOneS4Rules`.

**Design note**: the blocked case uses
`RuleResult.linear []`, not `.persistent []` or `.notApplicable`. This matters:
`modalStepBranchGen` (`Saturation.lean`) discards the rule's returned accessibility
component entirely when the result is `.notApplicable` (its `.notApplicable => none` arm
never touches `newAcc`), which would silently drop the loop-back edge. And `.persistent []`
never marks the source formula as expanded, which would cause the *same* blocked formula to
be re-selected by `b.findSome?` on every subsequent fuel step (wastefully re-adding the same
edge, and potentially starving other branch formulas of ever being processed within the
fuel budget). `.linear []` is what K's own fresh-world rules use for exactly this
one-shot-consumption shape (`Rules.lean`'s `diamondPos`/`boxNeg` arms), and correctly both
threads `newAcc` through and marks the source formula expanded. -/
def modalApplyOneS4 (φ₀ : Proposition Atom) : RuleApply Atom :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match blockingWorldS4 φ₀ b .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS4Rules sf b acc
    | .pos, .diamond φ =>
      match blockingWorldS4 φ₀ b .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS4Rules sf b acc
    | _, _ => modalApplyOneS4Rules sf b acc

/-- Guard spec (a)/(b), box-negative shape: `modalApplyOneS4 φ₀` at `F(□φ)@w` either (a)
blocks -- adding exactly one loop-back edge to an existing known world and minting no new
world -- or (b) does not block, in which case it reduces to the underlying K rule
(`modalApplyOne`), which mints exactly `modalNextWorld b`. This is the dispatch entry
point for the box-negative minting shape consumed by the pigeonhole world bound below. -/
lemma modalApplyOneS4_boxNeg_blocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hblock : blockingWorldS4 φ₀ b .neg φ w = some wBlock) :
    modalApplyOneS4 φ₀ ⟨.neg, .box φ, w⟩ b acc = (.linear [], acc.addEdge w wBlock) := by
  unfold modalApplyOneS4
  simp [hblock]

/-- Guard spec (b), box-negative shape, unblocked case: reduces to the underlying K rule. -/
lemma modalApplyOneS4_boxNeg_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) (hblock : blockingWorldS4 φ₀ b .neg φ w = none) :
    modalApplyOneS4 φ₀ ⟨.neg, .box φ, w⟩ b acc = modalApplyOne ⟨.neg, .box φ, w⟩ b acc := by
  unfold modalApplyOneS4
  simp only [hblock]
  rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg, modalApplyOneT_eq_of_not_boxPos_diaNeg]
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

/-- Guard spec (a)/(b), diamond-positive shape (dual of the box-negative pair): blocked case
adds exactly one loop-back edge and mints no new world. -/
lemma modalApplyOneS4_diaPos_blocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hblock : blockingWorldS4 φ₀ b .pos φ w = some wBlock) :
    modalApplyOneS4 φ₀ ⟨.pos, .diamond φ, w⟩ b acc = (.linear [], acc.addEdge w wBlock) := by
  unfold modalApplyOneS4
  simp [hblock]

/-- Guard spec (b), diamond-positive shape, unblocked case: reduces to the underlying K
rule, which mints exactly `modalNextWorld b`. -/
lemma modalApplyOneS4_diaPos_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) (hblock : blockingWorldS4 φ₀ b .pos φ w = none) :
    modalApplyOneS4 φ₀ ⟨.pos, .diamond φ, w⟩ b acc = modalApplyOne ⟨.pos, .diamond φ, w⟩ b acc := by
  unfold modalApplyOneS4
  simp only [hblock]
  rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg, modalApplyOneT_eq_of_not_boxPos_diaNeg]
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

/-- `modalApplyOneS4` agrees with `modalApplyOneS4Rules` (hence with the K/T/4 rule set)
outside the two minting shapes: the guard only ever intervenes at `F(□φ)@w`/`T(◇φ)@w`. -/
lemma modalApplyOneS4_eq_of_not_boxNeg_diaPos
    (φ₀ : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneS4 φ₀ sf b acc = modalApplyOneS4Rules sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneS4
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-! ## S4 Driver -/

/-- One-step branch expansion for the S4 (reflexive-transitive) tableau: the generic driver
(`modalStepBranchGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneS4 φ₀`.
Mirrors `modalStepBranchT` (`TDriver.lean`). -/
def modalStepBranchS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen (modalApplyOneS4 φ₀) b e acc

/-- Fuel-based expansion of a list of S4-system branches: the generic driver
(`modalExpandBranchesGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneS4 φ₀`.
Mirrors `modalExpandBranchesT`. -/
def modalExpandBranchesS4 (φ₀ : Proposition Atom)
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen (modalApplyOneS4 φ₀) branches expandedSets accs fuel

/-- The S4 (reflexive-transitive) modal tableau decision procedure: the generic entry point
(`modalTableauGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneS4 φ`, starting
the signed tableau from `F(φ)` at world `0`. `φ` is in scope as the guard's `φ₀` parameter
(Decision D1) throughout the run. **No** `RuleApplicationSpec` instance exists for
`modalApplyOneS4` (Correction 3) -- S4 reuses the generic driver definitionally only. -/
def modalTableauS4 (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen (modalApplyOneS4 φ) φ

/-! ## Key-Threaded S4 Step

`worldSetsDistinct`, stated over the *live* branch, is not a loop invariant (Gap 1): a
persistent step can fill in the one coordinate on which two worlds' relevant
sets differed, collapsing them. The fix (Option A2) threads a **stable per-world birth key**
list alongside `(b, e, acc)`: keys are fixed at minting time and never touched again, so a
lower-bound-style invariant stated over them survives every subsequent step. This is *the*
place S4 stops reusing `modalStepBranchGen` definitionally for **stepping** (it still reuses
`modalApplyOneS4 φ₀` -- the K/T/4 rule slot -- for all formula-level work); the S4 expansion
loop below needs an S4-specific driver regardless, so this cost is not incurred
twice. -/

/-! ## Box-Plus Birth-Key Enrichment: Additive Mint Definitions

`boxPlusPair`, `boxPlusExtraS4`, and `modalApplyOneS4KeyedMint` below must precede
`modalApplyOneS4Keyed`, which consumes the last of the three at its two unblocked mint arms.
The two shape lemmas for `modalApplyOneS4KeyedMint` live further down this file instead (after
`modalApplyOne_boxNeg_mint_fst_S4`/`_snd_S4` and their diamond duals, which they need). -/

/-- The additive boxed mint rule: `modalApplyOne`'s own result, with `boxPlusExtraS4` appended
to the payload whenever the result is `.linear` (the shape both minting arms of `modalApplyOne`
actually produce at the two shapes this is ever called at). The accessibility component is
preserved VERBATIM from `modalApplyOne`'s own result. Consumed below by `modalApplyOneS4Keyed`'s
two unblocked mint arms, replacing the raw `modalApplyOne sf b acc` fallthrough; `Rules.lean`
itself is never edited (shared by the K/T/B/S5 drivers and `FmpMeasure.lean`'s `_gen` lemmas,
where boxed transmission is not K-sound). -/
def modalApplyOneS4KeyedMint
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let result := modalApplyOne sf b acc
  match result.1 with
  | .linear forms => (.linear (forms ++ boxPlusExtraS4 b sf.label), result.2)
  | other => (other, result.2)

omit [Hashable Atom] in
/-- `modalApplyOneS4KeyedMint`'s accessibility component is VERBATIM `modalApplyOne`'s own,
for every `sf`, not just the two minting shapes: the `match` on `result.1` in the definition
above never rewrites `result.2`. Bridge fact letting every proof that only inspects the
accessibility component (never the payload list) swap the raw `modalApplyOne_*_mint_snd_S4`
lemmas straight through, unaffected by the mint payload's enrichment. -/
lemma modalApplyOneS4KeyedMint_snd_eq (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneS4KeyedMint sf b acc).snd = (modalApplyOne sf b acc).snd := by
  unfold modalApplyOneS4KeyedMint
  cases h : (modalApplyOne sf b acc).1 <;> simp [h]

omit [Hashable Atom] in
/-- Every result of `modalApplyOneS4KeyedMint` either coincides exactly with `modalApplyOne`'s
own result (every non-minting shape, where the match's `other` branch fires unchanged), or is
`modalApplyOne`'s `.linear` result with `boxPlusExtraS4` appended to the payload (the two
minting shapes, where the match's `.linear` branch fires). Generic bridge for every proof that
case-splits on `modalApplyOne`'s `RuleResult` shape and only needs the CONSTRUCTOR identity
(not the payload content) at each branch. -/
lemma modalApplyOneS4KeyedMint_fst_eq_or_linear
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneS4KeyedMint sf b acc).fst = (modalApplyOne sf b acc).fst ∨
    ∃ forms, (modalApplyOne sf b acc).fst = RuleResult.linear forms ∧
      (modalApplyOneS4KeyedMint sf b acc).fst =
        RuleResult.linear (forms ++ boxPlusExtraS4 b sf.label) := by
  cases h : (modalApplyOne sf b acc).1 with
  | linear forms => exact Or.inr ⟨forms, rfl, by simp only [modalApplyOneS4KeyedMint, h]⟩
  | branching brs => exact Or.inl (by simp only [modalApplyOneS4KeyedMint, h])
  | persistent forms => exact Or.inl (by simp only [modalApplyOneS4KeyedMint, h])
  | notApplicable => exact Or.inl (by simp only [modalApplyOneS4KeyedMint, h])

/-- The keys-aware S4 rule-application function, closing the
guard-vs-keys gap. Identical in shape to `modalApplyOneS4 φ₀` (same non-minting fallthrough to
`modalApplyOneS4Rules`/`modalApplyOneS4`), but at the two minting shapes consults
`blockingWorldS4Keyed φ₀ b keys` (the RECORDED-keys guard) instead of `blockingWorldS4` (the
live-set guard). This is what makes `modalStepBranchS4Keyed`'s `(b, e, acc)` bookkeeping and its
`keys` bookkeeping driven by the SAME decision -- required for `S4LoopInv.keyLowerBd` to remain
consistent with `S4LoopInv.keysDistinct`: if the two bookkeeping streams
used different guards, a world could be recorded in `keys` without ever actually being minted
onto the branch, breaking `keyLowerBd` (`k ⊆ relevantSetFinset φ₀ b w` fails when `w` was never
minted, since then `relevantSetFinset φ₀ b w = ∅ ⊉ k` for nonempty `k`). Reduces to
`modalApplyOneS4KeyedMint` (the additive box-plus mint, `modalApplyOne`'s own payload plus the
boxed members) at an unblocked minting shape -- same underlying K rule as `modalApplyOneS4`'s
own unblocked reduction (`modalApplyOneS4_boxNeg_unblocked_eq`/dual), just gated by a different
guard and additively enriched. `modalApplyOneS4`/`blockingWorldS4` are NOT modified or removed:
they remain the live-set-guarded artifact the Hintikka/truth-lemma bridges consume. -/
def modalApplyOneS4Keyed (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : RuleApply Atom :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS4KeyedMint sf b acc
    | .pos, .diamond φ =>
      match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS4KeyedMint sf b acc
    | _, _ => modalApplyOneS4 φ₀ sf b acc

/-- Guard spec, box-negative shape, blocked case (mirrors `modalApplyOneS4_boxNeg_blocked_eq`
for the keys-aware guard). -/
lemma modalApplyOneS4Keyed_boxNeg_blocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hblock : blockingWorldS4Keyed φ₀ b keys .neg φ w = some wBlock) :
    modalApplyOneS4Keyed φ₀ keys ⟨.neg, .box φ, w⟩ b acc = (.linear [], acc.addEdge w wBlock) := by
  unfold modalApplyOneS4Keyed
  simp [hblock]

/-- Guard spec, box-negative shape, unblocked case: reduces to the additive boxed mint
(`modalApplyOneS4KeyedMint`) -- `modalApplyOne`'s own K-rule payload plus the box-plus extra. -/
lemma modalApplyOneS4Keyed_boxNeg_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (φ : Proposition Atom) (w : WorldIndex)
    (hblock : blockingWorldS4Keyed φ₀ b keys .neg φ w = none) :
    modalApplyOneS4Keyed φ₀ keys ⟨.neg, .box φ, w⟩ b acc
      = modalApplyOneS4KeyedMint ⟨.neg, .box φ, w⟩ b acc := by
  unfold modalApplyOneS4Keyed
  simp [hblock]

/-- Guard spec, diamond-positive shape, blocked case (dual of the box-negative pair). -/
lemma modalApplyOneS4Keyed_diaPos_blocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hblock : blockingWorldS4Keyed φ₀ b keys .pos φ w = some wBlock) :
    modalApplyOneS4Keyed φ₀ keys ⟨.pos, .diamond φ, w⟩ b acc
      = (.linear [], acc.addEdge w wBlock) := by
  unfold modalApplyOneS4Keyed
  simp [hblock]

/-- Guard spec, diamond-positive shape, unblocked case: reduces to the additive boxed mint
(dual of `modalApplyOneS4Keyed_boxNeg_unblocked_eq`). -/
lemma modalApplyOneS4Keyed_diaPos_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (φ : Proposition Atom) (w : WorldIndex)
    (hblock : blockingWorldS4Keyed φ₀ b keys .pos φ w = none) :
    modalApplyOneS4Keyed φ₀ keys ⟨.pos, .diamond φ, w⟩ b acc
      = modalApplyOneS4KeyedMint ⟨.pos, .diamond φ, w⟩ b acc := by
  unfold modalApplyOneS4Keyed
  simp [hblock]

/-! ## Mint-Readiness: A Global, Non-Recursive Settledness Predicate

The repair for the keyed guard's unsoundness (`blockingWorldS4Keyed`'s docstring above) does
**not** edit this comparison predicate. Instead it restricts *when* a minting shape
(`F(□φ)@w`, `T(◇φ)@w`) is allowed to fire: only once every other rule that could still fire
anywhere on the branch has already fired. Delaying a mint until the branch has propagated
everything it currently can is what prevents a later sibling expansion from adding formulas to
a world's *live* content after that world's *recorded* key was already compared against -- the
exact mechanism the counterexample exploits.

**Design decision (deviation from the research report, deliberate).** A per-world formulation
("no unexpanded formula at `w`, and every predecessor of `w` is itself settled") would need a
well-foundedness argument that the accessibility record cannot supply: mint edges point to
strictly larger fresh worlds, but redirect edges (the very edges `blockingWorldS4Keyed`
licenses) may point to *smaller* worlds, and a reflexive self-block `w → w` is explicitly
permitted, so the predecessor relation can cycle. `modalNonMintCandidates` below instead states
settledness **globally**: a minting shape may fire only when no non-minting rule can fire
*anywhere* on the branch, not just at `w`. This is strictly stronger than the per-world
condition (it implies it), decidable by direct computation on `(b, e, acc, keys)` with no
recursion and no well-foundedness obligation at all. The key enabling fact is that
`modalApplyOneS4Rules` (`FrameRules.lean`) returns `.notApplicable` when a persistent rule's
output would be empty (nothing new to propagate), so "settled" is expressible as a plain
`RuleResult.isApplicable` check even though persistent formulas never leave the branch to enter
`e`. -/

/-- The non-minting candidate sublist of `b`: formulas that (1) are not one of the two minting
shapes, (2) have not yet been expanded, and (3) have some applicable rule under
`modalApplyOneS4Keyed φ₀ keys` (evaluated against the current `(b, acc)`, mirroring exactly the
per-formula call `modalStepBranchGen`'s own selection makes). This is the ordered stepper's
(companion phase) primary traversal list: consulting it before falling back to the old
`b.findSome?` traversal is what "settled-context scheduling" means -- a minting shape only
fires once this list is empty, i.e. once every non-minting rule that could still fire on the
branch has already fired. -/
def modalNonMintCandidates (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  b.filter (fun sf =>
    !modalMintShape sf && !(e.any (· == sf)) &&
      (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable)

/-- Every non-minting candidate is drawn from the branch `b`. -/
lemma modalNonMintCandidates_subset (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalNonMintCandidates φ₀ keys b e acc ⊆ b := by
  unfold modalNonMintCandidates
  exact List.filter_subset_self _

/-- Every non-minting candidate lies outside the expanded set `e`. -/
lemma modalNonMintCandidates_not_mem_expanded (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (h : sf ∈ modalNonMintCandidates φ₀ keys b e acc) : sf ∉ e := by
  unfold modalNonMintCandidates at h
  have hpred := (List.mem_filter.mp h).2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
  intro hmem
  exact absurd (show (sf == sf) = true by simp) (List.any_eq_false.mp hpred.1.2 sf hmem)

/-- **The settledness characterisation.** The non-minting candidate list is empty exactly when
no non-minting rule can fire anywhere on the branch: every branch formula is either a minting
shape, already expanded, or has no applicable rule under `modalApplyOneS4Keyed φ₀ keys`. Later
phases consume this as "the branch's propagation has settled". -/
lemma modalNonMintCandidates_eq_nil_iff (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalNonMintCandidates φ₀ keys b e acc = [] ↔
      ∀ sf ∈ b, modalMintShape sf = true ∨ sf ∈ e ∨
        (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable := by
  unfold modalNonMintCandidates
  rw [List.filter_eq_nil_iff]
  refine forall_congr' fun sf => imp_congr_right fun _ => ?_
  constructor
  · intro hnp
    by_cases hshape : modalMintShape sf = true
    · exact Or.inl hshape
    by_cases hexp : sf ∈ e
    · exact Or.inr (Or.inl hexp)
    refine Or.inr (Or.inr ?_)
    by_contra hne
    apply hnp
    simp only [Bool.not_eq_true] at hshape
    have hany : e.any (· == sf) = false := by
      rw [List.any_eq_false]
      intro x hx heq
      rw [beq_iff_eq] at heq
      subst heq
      exact hexp hx
    have happ : (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable = true := by
      cases hr : (modalApplyOneS4Keyed φ₀ keys sf b acc).1 with
      | notApplicable => exact absurd hr hne
      | linear _ => rfl
      | branching _ => rfl
      | persistent _ => rfl
    simp [hshape, hany, happ]
  · intro h hnp
    rcases h with hshape | hexp | hnotapp
    · simp [hshape] at hnp
    · have hany : e.any (· == sf) = true := List.any_eq_true.mpr ⟨sf, hexp, by simp⟩
      simp [hany] at hnp
    · simp [hnotapp, RuleResult.isApplicable] at hnp

/-- The S4-specific keyed one-step branch expansion: same selected formula (`b.findSome?` over
the same "already expanded" guard) and same rule application (`modalApplyOneS4Keyed φ₀ keys`,
above) as the `(newBranches, newExpandedSets, newAcc)` triple -- additionally threads
a `keys` list recording every known world's stable birth content. On a call at one of the two
minting shapes that is **not** blocked (`blockingWorldS4Keyed φ₀ b keys s φ w = none`), the
underlying rule mints `modalNextWorld b`, so `keys` gains the entry `(modalNextWorld b,
successorBirthContent φ₀ b s φ w)`. On every other call (blocked minting-shaped, or a
non-minting shape entirely), no world is minted and `keys` is unchanged. The keys' computation
below re-derives the SAME `blockingWorldS4Keyed` decision `modalApplyOneS4Keyed` already made
internally (rather than threading it out), keeping this definition's shape close to the
un-keyed original above for auditability. -/
def modalStepBranchS4Keyed (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility ×
            List (WorldIndex × Finset (Sign × Proposition Atom))) :=
  b.findSome? fun sf =>
    if e.any (· == sf) then none
    else
      let (result, newAcc) := modalApplyOneS4Keyed φ₀ keys sf b acc
      let keys' :=
        match sf.sign, sf.formula with
        | .neg, .box φ =>
          match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
          | some _ => keys
          | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)]
        | .pos, .diamond φ =>
          match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
          | some _ => keys
          | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)]
        | _, _ => keys
      match result with
      | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
      | .branching branches =>
        some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
      | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
      | .notApplicable => none

/-! ## Ordered Stepper: Settled-Context Scheduling

`modalStepBranchS4KeyedOrdered` is the reordered successor to `modalStepBranchS4Keyed` above: it
consults the non-minting candidates (`modalNonMintCandidates`) FIRST, falling back to the
literal old `b.findSome?` traversal only once no non-minting rule can fire. This is
"settled-context scheduling": a minting shape (`F(□φ)@w` or `T(◇φ)@w`) only fires once every
non-minting rule on the branch has already fired, which is the reachability-restriction
prerequisite the S4-keyed guard's soundness argument needs (Phases 9-11 of this task's plan).
`modalStepBranchS4Keyed` itself is left completely untouched -- its source above this comment is
unchanged, and it is the literal fallback branch of the ordered stepper below -- so the landed
completeness line (`modalTableauS4Keyed_complete`) stays green throughout this retrofit.
Retirement of `modalStepBranchS4Keyed` in favour of this ordered successor is planned future
work, once the ordered driver and its own completeness/soundness theorems land. -/

/-- The per-formula rule-application body shared, verbatim, by `modalStepBranchS4Keyed`'s
`b.findSome?` traversal and `modalStepBranchS4KeyedOrdered`'s two-stage traversal below: the same
`modalApplyOneS4Keyed` call, the same `keys'` computation re-deriving the `blockingWorldS4Keyed`
decision, and the same four-way result-shape packaging. Factored out under its own name purely
so the structural lemmas below can name it directly; `modalStepBranchS4Keyed` itself does not use
this definition and is not touched by its introduction (see
`modalStepBranchS4Keyed_eq_findSome_body` for the bridge between the two). -/
def modalStepBranchS4KeyedBody (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility ×
            List (WorldIndex × Finset (Sign × Proposition Atom))) :=
  if e.any (· == sf) then none
  else
    let (result, newAcc) := modalApplyOneS4Keyed φ₀ keys sf b acc
    let keys' :=
      match sf.sign, sf.formula with
      | .neg, .box φ =>
        match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)]
      | .pos, .diamond φ =>
        match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)]
      | _, _ => keys
    match result with
    | .linear newForms => some ([newForms ++ b], [e ++ [sf]], newAcc, keys')
    | .branching branches =>
      some (branches.map (· ++ b), branches.map (fun _ => e ++ [sf]), newAcc, keys')
    | .persistent newForms => some ([newForms ++ b], [e], newAcc, keys')
    | .notApplicable => none

/-- `modalStepBranchS4Keyed`'s `b.findSome?` traversal is literally `b.findSome?` applied to
`modalStepBranchS4KeyedBody`: this bridges the untouched original definition to the named body
above, so later lemmas can be stated once against the named body and reused for both
traversals. -/
lemma modalStepBranchS4Keyed_eq_findSome_body (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    modalStepBranchS4Keyed φ₀ b e acc keys =
      b.findSome? (modalStepBranchS4KeyedBody φ₀ b e acc keys) := rfl

/-- Every non-minting candidate makes the shared per-formula body evaluate to `some`, never
`none`: unfolding `modalNonMintCandidates`'s filter gives `sf ∉ e` (ruling out the body's
`if e.any ... then none` guard) and `(modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable`
(ruling out the body's `.notApplicable => none` result arm) -- the body's only two
`none`-producing arms. Private: only the two public corollaries below (`_eq_none_iff` and the
`_cases` helper feeding `_selected_mem`/`_mintReady`) consume it directly. -/
private lemma modalStepBranchS4KeyedBody_isSome_of_mem_nonMintCandidates (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (h : sf ∈ modalNonMintCandidates φ₀ keys b e acc) :
    (modalStepBranchS4KeyedBody φ₀ b e acc keys sf).isSome := by
  have hne : sf ∉ e := modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc sf h
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hne hx
  have happ : (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable = true := by
    unfold modalNonMintCandidates at h
    have hpred := (List.mem_filter.mp h).2
    simp only [Bool.and_eq_true] at hpred
    exact hpred.2
  unfold modalStepBranchS4KeyedBody
  rw [if_neg (by simp [hany])]
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc⟩
  rw [hpair] at happ
  cases hr : result with
  | notApplicable => rw [hr] at happ; simp [RuleResult.isApplicable] at happ
  | linear _ => simp
  | branching _ => simp
  | persistent _ => simp

/-- **Corollary A.** The non-minting candidate list is empty exactly when the primary
`findSome?` scan over it (using the shared body) finds nothing -- the empty-list case is
`List.findSome?_nil`; the nonempty case uses the key fact above (every candidate makes the body
`isSome`) together with `List.findSome?_isSome_iff`. -/
private lemma modalNonMintCandidates_eq_nil_iff_findSome_eq_none (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    modalNonMintCandidates φ₀ keys b e acc = [] ↔
      (modalNonMintCandidates φ₀ keys b e acc).findSome?
        (modalStepBranchS4KeyedBody φ₀ b e acc keys) = none := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    by_contra hne
    rw [List.findSome?_eq_none_iff] at h
    obtain ⟨sf, hsf⟩ := List.exists_mem_of_ne_nil _ hne
    have hsome := modalStepBranchS4KeyedBody_isSome_of_mem_nonMintCandidates φ₀ b e acc keys sf hsf
    rw [h sf hsf] at hsome
    simp at hsome

/-- The reordered one-step branch expansion: same per-formula rule application as
`modalStepBranchS4Keyed` (`modalStepBranchS4KeyedBody`, above), but a different traversal order.
`findSome?` first scans `modalNonMintCandidates φ₀ keys b e acc` -- the non-minting, not-yet
-expanded, currently applicable formulas -- and only falls back to the literal old `b.findSome?`
traversal (`modalStepBranchS4Keyed φ₀ b e acc keys`) once that scan returns `none`, i.e. once the
branch has settled (no non-minting rule can still fire anywhere on it). Successor to
`modalStepBranchS4Keyed`, which this definition will eventually retire. -/
def modalStepBranchS4KeyedOrdered (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility ×
            List (WorldIndex × Finset (Sign × Proposition Atom))) :=
  match (modalNonMintCandidates φ₀ keys b e acc).findSome?
      (modalStepBranchS4KeyedBody φ₀ b e acc keys) with
  | some r => some r
  | none => modalStepBranchS4Keyed φ₀ b e acc keys

/-- **Structural case split.** Whenever the ordered stepper returns `some`, either (1) the
result came from the primary candidate scan -- some non-minting candidate's body evaluates to
exactly that result -- or (2) the candidate list was already empty and the result came from the
literal fallback traversal. This is the single case split every other structural lemma below
factors through. -/
lemma modalStepBranchS4KeyedOrdered_cases (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    (∃ sf ∈ modalNonMintCandidates φ₀ keys b e acc,
        modalStepBranchS4KeyedBody φ₀ b e acc keys sf = some (newBs, newExps, newAcc, keys')) ∨
    (modalNonMintCandidates φ₀ keys b e acc = [] ∧
        modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) := by
  unfold modalStepBranchS4KeyedOrdered at hstep
  cases hcase : (modalNonMintCandidates φ₀ keys b e acc).findSome?
      (modalStepBranchS4KeyedBody φ₀ b e acc keys) with
  | none =>
    rw [hcase] at hstep
    right
    exact ⟨(modalNonMintCandidates_eq_nil_iff_findSome_eq_none φ₀ b e acc keys).mpr hcase, hstep⟩
  | some r =>
    rw [hcase] at hstep
    left
    obtain ⟨sf, hsf_mem, hsf_body⟩ := List.exists_of_findSome?_eq_some hcase
    exact ⟨sf, hsf_mem, hsf_body.trans hstep⟩

/-- `modalStepBranchS4KeyedOrdered ... = none ↔ modalStepBranchS4Keyed ... = none`. The linchpin
that lets later phases (the saturation step in particular) transfer facts about the old
stepper's termination condition to the new one without re-deriving anything: if the ordered
stepper reaches the fallback, both sides are the literal same expression; if it does not, both
sides are provably `some _ ≠ none` (a primary-scan hit forces the old traversal to also find
something, since `sf` is in `b` and the shared body applied to it is not `none`). -/
lemma modalStepBranchS4KeyedOrdered_eq_none_iff (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    modalStepBranchS4KeyedOrdered φ₀ b e acc keys = none ↔
      modalStepBranchS4Keyed φ₀ b e acc keys = none := by
  unfold modalStepBranchS4KeyedOrdered
  cases hcase : (modalNonMintCandidates φ₀ keys b e acc).findSome?
      (modalStepBranchS4KeyedBody φ₀ b e acc keys) with
  | none => rfl
  | some r =>
    obtain ⟨sf, hsf_mem, hsf_body⟩ := List.exists_of_findSome?_eq_some hcase
    have hsf_b : sf ∈ b := modalNonMintCandidates_subset φ₀ keys b e acc hsf_mem
    have hne : modalStepBranchS4Keyed φ₀ b e acc keys ≠ none := by
      rw [modalStepBranchS4Keyed_eq_findSome_body]
      intro hcontra
      rw [List.findSome?_eq_none_iff] at hcontra
      have := hcontra sf hsf_b
      rw [hsf_body] at this
      simp at this
    simp only [reduceCtorEq, false_iff]
    exact hne

/-- Whenever the ordered stepper returns `some`, the selected formula is in `b`, not in `e`, and
the returned tuple has one of the same four result shapes the shared body's match produces.
Stated so that later phases (the termination-measure re-verification in particular) can consume
it directly in place of the `List.exists_of_findSome?_eq_some` extraction the old measure proof
performs against `modalStepBranchS4Keyed`. -/
lemma modalStepBranchS4KeyedOrdered_selected_mem (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∃ sf ∈ b, sf ∉ e ∧
      modalStepBranchS4KeyedBody φ₀ b e acc keys sf = some (newBs, newExps, newAcc, keys') := by
  rcases modalStepBranchS4KeyedOrdered_cases φ₀ b e acc keys newBs newExps newAcc keys' hstep with
    ⟨sf, hsf_mem, hsf_body⟩ | ⟨-, hfallback⟩
  · refine ⟨sf, modalNonMintCandidates_subset φ₀ keys b e acc hsf_mem,
      modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc sf hsf_mem, hsf_body⟩
  · rw [modalStepBranchS4Keyed_eq_findSome_body] at hfallback
    obtain ⟨sf, hsf_mem, hsf_body⟩ := List.exists_of_findSome?_eq_some hfallback
    refine ⟨sf, hsf_mem, ?_, hsf_body⟩
    intro hmem
    have : modalStepBranchS4KeyedBody φ₀ b e acc keys sf = none := by
      unfold modalStepBranchS4KeyedBody
      rw [if_pos (List.any_eq_true.mpr ⟨sf, hmem, by simp⟩)]
    rw [this] at hsf_body
    simp at hsf_body

/-- **Settled-context scheduling, soundness form.** If a step's result could only have arisen
from a minting-shaped formula (i.e. every formula whose shared body produces that exact result
is a minting shape), the non-minting candidate list must already have been empty at the time of
selection: a minting shape can only fire once every non-minting rule on the branch has already
fired. This is the fact that carries settled-context scheduling into the soundness argument
(Phases 9-11 of this task's plan) and is the entire point of the reordering. -/
lemma modalStepBranchS4KeyedOrdered_mintReady (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys'))
    (hmint : ∀ sf, modalStepBranchS4KeyedBody φ₀ b e acc keys sf =
        some (newBs, newExps, newAcc, keys') → modalMintShape sf = true) :
    modalNonMintCandidates φ₀ keys b e acc = [] := by
  rcases modalStepBranchS4KeyedOrdered_cases φ₀ b e acc keys newBs newExps newAcc keys' hstep with
    ⟨sf, hsf_mem, hsf_body⟩ | ⟨hcandidates, -⟩
  · exact absurd (hmint sf hsf_body) (by
      unfold modalNonMintCandidates at hsf_mem
      have hpred := (List.mem_filter.mp hsf_mem).2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
      simp [hpred.1.1])
  · exact hcandidates

/-! ## Origin-Edge Invariant

**The gap this closes.** `S4LoopInv.keyLowerBd` gives `key(wBlock) ⊆ relevantSetFinset φ₀ b
wBlock`, but a redirect edge `v → wBlock`'s propagation-adequacy obligation needs the actual
*boxed* form `T(□ψ)@wBlock ∈ b` for every `T(□ψ)@v ∈ b` -- `keyLowerBd` alone only recovers the
unwrapped `T(ψ)@wBlock ∈ b` (the recorded key stores unwrapped box-context, per
`successorBirthContent`'s docstring). The missing step is *where `wBlock`'s key came from*: every
non-root key was recorded at a mint, and that mint recorded an edge. `keysOriginS4` records this
origin edge as a standalone auxiliary, letting mint-readiness act on an edge that already exists.

**Design decision -- auxiliary, not an `S4LoopInv` field** (flagged deviation from an earlier,
rejected `keysOrigin` sketch): adding a field to `S4LoopInv` would reopen the
already-finalized struct design and force re-proof of the unordered line
(`modalStepBranchS4_preserves_S4LoopInv`), which this plan is committed to leaving byte-for-byte
unchanged until this driver's retirement. The codebase already sets this precedent twice:
`keysWorldsKnown` ("not an `S4LoopInv` field: adding one would reopen the already-finalized
struct design", above) and `worldsContiguousS4` (below). `keysOriginS4` is threaded the same
way: an extra hypothesis/conclusion alongside `S4LoopInv` at call sites, never a struct field.

**Design decision -- no historical branch in the statement** (flagged deviation): stated over
the *current* branch `b` and *current* `acc`, not a historical pre-mint branch `b_birth ⊆ b`.
This bakes in the consequence directly (`T(s)@u ∈ b` rather than `∈ b_birth` plus a subset side
condition), which makes preservation under branch growth immediate: the `∈ b` disjunct simply
persists as `b` grows, with no `b_birth` bookkeeping to carry. -/

omit [Hashable Atom] in
/-- `modalApplyOneS4Rules`'s `.fst` component at a box-positive shape, in terms of the
underlying `modalApplyOneT` result and the 4-rule propagation `modalFourBoxProp` -- one layer
above `modalApplyOneT_boxPos_fst` (`TDriver.lean`), same proof shape. -/
lemma modalApplyOneS4Rules_boxPos_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4Rules (⟨.pos, .box φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOneT (⟨.pos, .box φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent tForms =>
            .persistent (tForms ++
              (modalFourBoxProp b acc φ w).filter (fun x => !(tForms.any (· == x))))
          | .notApplicable =>
            if (modalFourBoxProp b acc φ w).isEmpty then .notApplicable
            else .persistent (modalFourBoxProp b acc φ w)
          | other => other) := by
  simp only [modalApplyOneS4Rules]
  cases (modalApplyOneT (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Dual of `modalApplyOneS4Rules_boxPos_fst` for the diamond-negative shape. -/
lemma modalApplyOneS4Rules_diaNeg_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4Rules (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent tForms =>
            .persistent (tForms ++
              (modalFourDiaNegProp b acc φ w).filter (fun x => !(tForms.any (· == x))))
          | .notApplicable =>
            if (modalFourDiaNegProp b acc φ w).isEmpty then .notApplicable
            else .persistent (modalFourDiaNegProp b acc φ w)
          | other => other) := by
  simp only [modalApplyOneS4Rules]
  cases (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- If the 4-rule box-positive propagation from `w` is nonempty, `modalApplyOneS4Rules` is
applicable at `T(□φ)@w` -- regardless of what `modalApplyOneT`'s own result was (persistent,
notApplicable, or, vacuously, other), since the `.notApplicable` arm promotes to `.persistent`
exactly when the propagation list is nonempty and the other two arms are unconditionally not
`.notApplicable`. -/
private lemma modalApplyOneS4Rules_boxPos_not_notApplicable_of_fourBoxProp_ne_nil
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex)
    (hne : modalFourBoxProp b acc φ w ≠ []) :
    (modalApplyOneS4Rules (⟨.pos, .box φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst ≠ .notApplicable := by
  rw [modalApplyOneS4Rules_boxPos_fst]
  cases (modalApplyOneT (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
  | linear _ => simp
  | branching _ => simp
  | persistent _ => simp
  | notApplicable =>
    split_ifs with hemp
    · exact absurd (List.isEmpty_iff.mp hemp) hne
    · simp

/-- `modalApplyOneS4Keyed` reduces to `modalApplyOneS4Rules` at a box-positive shape: both
`modalApplyOneS4Keyed`'s own guard-consulting arms (`.neg, .box`/`.pos, .diamond`) and
`modalApplyOneS4`'s (same two shapes) fail to match `.pos, .box`, so both catch-all arms fire
in sequence, definitionally. -/
lemma modalApplyOneS4Keyed_boxPos_eq_S4Rules (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneS4Keyed φ₀ keys (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc := rfl

/-- Dual of `modalApplyOneS4Keyed_boxPos_eq_S4Rules` for the diamond-negative shape. -/
lemma modalApplyOneS4Keyed_diaNeg_eq_S4Rules (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneS4Keyed φ₀ keys (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc := rfl

omit [Hashable Atom] in
/-- Dual of `modalApplyOneS4Rules_boxPos_not_notApplicable_of_fourBoxProp_ne_nil` for the
diamond-negative shape. -/
private lemma modalApplyOneS4Rules_diaNeg_not_notApplicable_of_fourDiaNegProp_ne_nil
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex)
    (hne : modalFourDiaNegProp b acc φ w ≠ []) :
    (modalApplyOneS4Rules (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst ≠ .notApplicable := by
  rw [modalApplyOneS4Rules_diaNeg_fst]
  cases (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
  | linear _ => simp
  | branching _ => simp
  | persistent _ => simp
  | notApplicable =>
    split_ifs with hemp
    · exact absurd (List.isEmpty_iff.mp hemp) hne
    · simp

/-! ### The Witness Disjunct (Gate)

`successorBirthContent φ₀ b s φ w = insert (s, φ) (filter ...)` inserts the witness pair `(s, φ)`
**unconditionally**, so `(Sign.pos, ψ) ∈ key(wBlock)` splits into case (b) (closed via
`blockedRedirect_boxctx_mem_of_boxOrigin`, now archived at
`Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean`) and case (a): `(pos, ψ)` is the origin mint's own
witness, i.e. the origin shape was `T(◇ψ)@u`, and `T(□ψ)@u` need not be on the branch. This
section originally recorded a verdict that **case (a) is unreachable ("R1")**, reasoning that the
witness disjunct of `keysOriginS4` never needs to supply the boxed form `T(□ψ)@wBlock` because
the only consumer queries the unwrapped witness content instead. That verdict was **refuted** by
`reports/02_redirect-inertness-divergence-audit.md` (§2.2): case (a) is exactly the
witness-collision configuration that made `blockedRedirect_boxctx_mem` false (a reachable state
where an unrelated world independently acquires both the diamond mint-trigger and the
box-context formula, collapsing to the same singleton key). Case (a) does bite; R1 was wrong --
see the removed-lemma comment above (`### Redirect-Inertness Assembly`) for the corrected
analysis. -/

/-! ## Minting-Content Groundwork: towards `successorBirthContent` matching the actual
K-minting payload

`successorBirthContent` was *designed* to match `modalApplyOne`'s box-neg/diamond-pos minting
payload (its own docstring): `keyLowerBd`'s minting case needs the fresh world's
`relevantSetFinset` (over the POST-step branch) to equal the prospective birth content computed
PRE-step. This section lands the REUSABLE groundwork for that equality (subformula-membership
extraction so the witness lands in `signedSubfmls φ₀`, plus the literal `.fst` unfolding of
`modalApplyOne` at both minting shapes); the equality itself (a pure Lean `Bool`-vs-`Prop`
proof-engineering matter, not a further structural gap) is closed in the "Minting-Content
Equality Closure" section below. -/

omit [Hashable Atom] in
/-- `modalApplyOne`'s box-negative minting shape, unfolded directly to its literal `.linear`
payload (mirrors `FiveSimplification.lean`'s file-private `modalApplyOne_boxNeg_mint_fst`). -/
lemma modalApplyOne_boxNeg_mint_fst_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = RuleResult.linear ((⟨.neg, φ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ::
        (boxPositivesOf b).filterMap (fun (ψ, src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
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
          else none)) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_neg]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  rfl

omit [Hashable Atom] in
/-- `modalApplyOne`'s diamond-positive minting shape, unfolded directly (dual of
`modalApplyOne_boxNeg_mint_fst`; mirrors `FiveSimplification.lean`'s file-private
`modalApplyOne_diamondPos_mint_fst`). -/
lemma modalApplyOne_diamondPos_mint_fst_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst
      = RuleResult.linear ((⟨.pos, φ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ::
        (boxPositivesOf b).filterMap (fun (ψ, src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
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
          else none)) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  rfl

omit [Hashable Atom] in
/-- `modalApplyOne`'s box-negative minting shape adds exactly one fresh edge, from the source
world to the freshly-minted witness `modalNextWorld b`. Mirrors `modalApplyOne_boxNeg_mint_fst_S4`
(same proof technique), extracting `.snd` instead of `.fst`. -/
lemma modalApplyOne_boxNeg_mint_snd_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = acc.addEdge w (modalNextWorld b) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_neg]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]

omit [Hashable Atom] in
/-- `modalApplyOne`'s diamond-positive minting shape adds exactly one fresh edge, from the
source world to the freshly-minted witness `modalNextWorld b`. Dual of
`modalApplyOne_boxNeg_mint_snd_S4`. -/
lemma modalApplyOne_diamondPos_mint_snd_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd
      = acc.addEdge w (modalNextWorld b) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]

/-! ## Box-Plus Birth-Key Enrichment: Mint Shape Lemmas

`boxPlusPair`, `boxPlusExtraS4`, and `modalApplyOneS4KeyedMint` live earlier in this file
(immediately before `def modalApplyOneS4Keyed`, which now consumes `modalApplyOneS4KeyedMint`
at its two unblocked mint arms). The two shape lemmas below live here instead, since they need
`modalApplyOne_boxNeg_mint_fst_S4`/`_snd_S4` and their diamond duals, which are declared above
this point. -/

omit [Hashable Atom] in
/-- `modalApplyOneS4KeyedMint`'s box-negative minting shape, unfolded directly to the full
result pair: `modalApplyOne`'s own payload (`modalApplyOne_boxNeg_mint_fst_S4`) with
`boxPlusExtraS4` appended, and the accessibility component unchanged from `modalApplyOne`'s own
edge (`modalApplyOne_boxNeg_mint_snd_S4`). Drop-in replacement shape for
`modalApplyOne_boxNeg_mint_fst_S4`, extended to the full pair since callers need both
components. -/
lemma modalApplyOneS4KeyedMint_boxNeg_eq_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneS4KeyedMint (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc
      = (RuleResult.linear (((⟨.neg, φ, modalNextWorld b⟩ :
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
            else none)) ++ boxPlusExtraS4 b w),
        acc.addEdge w (modalNextWorld b)) := by
  simp only [modalApplyOneS4KeyedMint, modalApplyOne_boxNeg_mint_fst_S4,
    modalApplyOne_boxNeg_mint_snd_S4]

omit [Hashable Atom] in
/-- Dual of `modalApplyOneS4KeyedMint_boxNeg_eq_S4`, diamond-positive shape. -/
lemma modalApplyOneS4KeyedMint_diaPos_eq_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneS4KeyedMint (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc
      = (RuleResult.linear (((⟨.pos, φ, modalNextWorld b⟩ :
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
            else none)) ++ boxPlusExtraS4 b w),
        acc.addEdge w (modalNextWorld b)) := by
  simp only [modalApplyOneS4KeyedMint, modalApplyOne_diamondPos_mint_fst_S4,
    modalApplyOne_diamondPos_mint_snd_S4]

omit [Hashable Atom] in
/-- `modalApplyOneS4KeyedMint`'s box-negative minting shape, existential form: the additive
boxed mint's payload still HEADS with the raw witness `F(ψ)@w'`, for SOME (opaque) remainder --
mirrors `modalApplyOne_boxNeg_witness`, extended with `boxPlusExtraS4` folded into the opaque
`rest`. Used by proofs that only need the witness's head position, not the full literal payload
(`Rules.lean`'s `modalApplyOne_boxNeg_witness` is the raw-K analogue). -/
lemma modalApplyOneS4KeyedMint_boxNeg_witness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4KeyedMint (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneS4KeyedMint (⟨.neg, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_boxNeg_witness b acc ψ w
  refine ⟨?_, rest ++ boxPlusExtraS4 b w, ?_⟩
  · simp only [modalApplyOneS4KeyedMint, hfst, hsnd]
  · simp only [modalApplyOneS4KeyedMint, hfst, List.cons_append]

omit [Hashable Atom] in
/-- Dual of `modalApplyOneS4KeyedMint_boxNeg_witness`, diamond-positive shape. -/
lemma modalApplyOneS4KeyedMint_diaPos_witness
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4KeyedMint (⟨.pos, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = acc.addEdge w (modalNextWorld b) ∧
      ∃ rest,
        (modalApplyOneS4KeyedMint (⟨.pos, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
                rest) := by
  obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_diamondPos_witness b acc ψ w
  refine ⟨?_, rest ++ boxPlusExtraS4 b w, ?_⟩
  · simp only [modalApplyOneS4KeyedMint, hfst, hsnd]
  · simp only [modalApplyOneS4KeyedMint, hfst, List.cons_append]

/-! ## Minting-Content Universe-Membership (groundwork for `bClosure`)

S4-local restatements of `FmpMeasure.lean`'s file-private subformula-closure facts for the
world-preserving and fresh-world minting rules
(`mem_boxPositivesOf`/`boxProps_outputs_subset`/`diaNegProps_outputs_subset`/
`modalApplyOne_diamondPos_outputs_subset`/`modalApplyOne_boxNeg_outputs_subset`), retargeted
from `modalUniverse`/`modalWorldBound` to `modalUniverseS4`/`modalWorldBoundS4`. These give the
`modalUniverseS4 φ₀` membership bound for `modalApplyOne`'s two minting shapes' literal output
content (`modalApplyOne_boxNeg_mint_fst_S4`/`modalApplyOne_diamondPos_mint_fst_S4`'s payload),
consumed by `modalStepBranchS4_preserves_bClosure`'s two minting-shape cases. -/

omit [Hashable Atom] in
/-- Shared closure fact for the `boxProps` group propagated by both fresh-world rules. S4-local
restatement of `FmpMeasure.lean`'s file-private `boxProps_outputs_subset`. -/
private lemma boxProps_outputs_subset_S4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀) :
    ∀ x ∈ (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex :=
            ⟨.pos, ψ, modalNextWorld b⟩
          if b.any (· == sf') then none else some sf'
        else none),
    x ∈ modalUniverseS4 φ₀ := by
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
      have hψsub : (Proposition.box ψ) ∈ modalSubfmls φ₀ :=
        modalUniverseS4_mem_formula (hb _ hψbox)
      have hψmem : ψ ∈ modalSubfmls (Proposition.box ψ) := by simp [modalSubfmls]
      exact mem_modalUniverseS4_of hwbound (modalSubfmls_trans hψmem hψsub)
  · simp at heq

omit [Hashable Atom] in
/-- Shared closure fact for the `diaNegProps` group propagated by both fresh-world rules.
S4-local restatement of `FmpMeasure.lean`'s file-private `diaNegProps_outputs_subset`. -/
private lemma diaNegProps_outputs_subset_S4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀) :
    ∀ x ∈ b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .diamond ψ =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none),
    x ∈ modalUniverseS4 φ₀ := by
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
        have hψsub : (Proposition.diamond ψ) ∈ modalSubfmls φ₀ := by
          have hmem := modalUniverseS4_mem_formula (hb sf' hsf'mem)
          rwa [hform] at hmem
        have hψmem : ψ ∈ modalSubfmls (Proposition.diamond ψ) := by simp [modalSubfmls]
        exact mem_modalUniverseS4_of hwbound (modalSubfmls_trans hψmem hψsub)
    · simp at heq
  · simp at heq

omit [Hashable Atom] in
/-- `diamondPos`: `T(◇φ)@w` creates a fresh world `w' = modalNextWorld b` and emits three
groups at `w'`: the witness, propagated box-positives, and propagated diamond-negatives. All
three groups stay inside `U_{S4}(φ₀)` given the branch invariant `hb`, the source membership
`hsf`, and the STRICT world-bound hypothesis `hW`. S4-local restatement of `FmpMeasure.lean`'s
`modalApplyOne_diamondPos_outputs_subset`. -/
lemma modalApplyOne_diamondPos_outputs_subset_S4
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsf : (⟨.pos, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hW : modalMaxWorld b < modalWorldBoundS4 φ₀) :
    ∀ x ∈ (((⟨.pos, φ, modalNextWorld b⟩ :
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
        else none)) ++ boxPlusExtraS4 b w),
    x ∈ modalUniverseS4 φ₀ := by
  have hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀ := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ₀ :=
    modalUniverseS4_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) := by simp [modalSubfmls]
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with ((rfl | hbox) | hdia) | hextra
  · exact mem_modalUniverseS4_of hwbound (modalSubfmls_trans hφmem hsrc)
  · exact boxProps_outputs_subset_S4 φ₀ b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset_S4 φ₀ b w hb hwbound x hdia
  · exact boxPlusExtraS4_outputs_subset_S4 φ₀ b w hb hwbound x hextra

omit [Hashable Atom] in
/-- `boxNeg`: `F(□φ)@w` creates a fresh world `w' = modalNextWorld b` and emits three groups at
`w'`: the witness, propagated box-positives, and propagated diamond-negatives. Identical
structure to `modalApplyOne_diamondPos_outputs_subset_S4` except the witness is directly `φ`
(a subformula of `.box φ` itself) and negatively signed. S4-local restatement of
`FmpMeasure.lean`'s `modalApplyOne_boxNeg_outputs_subset`. -/
lemma modalApplyOne_boxNeg_outputs_subset_S4
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsf : (⟨.neg, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hW : modalMaxWorld b < modalWorldBoundS4 φ₀) :
    ∀ x ∈ (((⟨.neg, φ, modalNextWorld b⟩ :
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
        else none)) ++ boxPlusExtraS4 b w),
    x ∈ modalUniverseS4 φ₀ := by
  have hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀ := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.box φ) ∈ modalSubfmls φ₀ := modalUniverseS4_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls (Proposition.box φ) := by simp [modalSubfmls]
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with ((rfl | hbox) | hdia) | hextra
  · exact mem_modalUniverseS4_of hwbound (modalSubfmls_trans hφmem hsrc)
  · exact boxProps_outputs_subset_S4 φ₀ b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset_S4 φ₀ b w hb hwbound x hdia
  · exact boxPlusExtraS4_outputs_subset_S4 φ₀ b w hb hwbound x hextra

end Cslib.Logic.Modal.Tableau

end
