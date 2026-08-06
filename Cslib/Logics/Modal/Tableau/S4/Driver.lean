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

**Built across two phases at a verified-acyclic seam.** The first half holds the *definitions*
and their immediate equation/shape/witness lemmas (49 declarations); this second half adds the
remaining composite lemmas -- known-worlds and universe-membership facts, the `branch_superset`
pair, the `RuleApplySt` bridge to the generic driver, and the trailing `hasEdge`/keys-independence
facts (39 declarations). The two halves were verified reference-acyclic (zero forward edges from
the first half into the second) before the split.

## Main Definitions
- `modalApplyOneS4`, `modalStepBranchS4`, `modalExpandBranchesS4`, `modalTableauS4`: the
  unkeyed S4 rule-application and driver family.
- `modalApplyOneS4KeyedMint`, `modalApplyOneS4Keyed`: the keyed minting guard and rule
  application.
- `modalNonMintCandidates`: the non-minting candidate sublist (settled-context scheduling).
- `modalStepBranchS4Keyed`, `modalStepBranchS4KeyedBody`, `modalStepBranchS4KeyedOrdered`: the
  keyed step-branch family, culminating in the ordered stepper.
- `modalExpandBranchesS4Keyed`, `modalExpandBranchesS4KeyedOrdered`: the keyed branch-expansion
  drivers.
- `modalApplyOneS4KeyedSt`: the state-threaded `RuleApplySt` instantiation bridging to the
  generic driver (`GenericDriver.lean`).

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
- `modalStepBranchS4Keyed{,Ordered}_branch_superset`: the step-branch monotonicity pair.
- `modalStepBranchS4Keyed_result_{keys,acc}_eq`, `_keys_subset`,
  `modalStepBranchS4KeyedOrdered_keys_subset`: keys-threading facts the invariant modules
  consume.
- The `modalApplyOne{T,S4Rules,S4Keyed}_*_{known,universe}_S4` groups: the known-worlds and
  universe-membership composite facts (the module's Part 2 namesake).
- `modalApplyOneS4KeyedSt_proj`, `_eq`, `modalStepBranchGenSt_eq_S4Keyed`,
  `modalExpandBranchesGenSt_eq_S4Keyed`: the `RuleApplySt` bridge theorems.
- `modalApplyOneS4Keyed_fst_eq_of_not_box`, `_hasEdge_mono`,
  `modalHintikkaClauseGen_S4Keyed_keys_indep`, `_boxNeg_ne_notApplicable`,
  `_diaPos_ne_notApplicable`: the trailing structural facts the redirect and invariant layers
  consume.
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

/-- Every branch `modalStepBranchS4Keyed` produces is a superset of the pre-step branch: each
output branch has the literal shape `X ++ b` (new formulas prepended, `b` untouched at the
tail), regardless of which rule fired or whether the result was `.linear`/`.branching`/
`.persistent`. This is what lets OLD keys' `keyLowerBd` obligation survive any step via
`relevantSetFinset_mono`, with no need to know which rule actually fired. -/
lemma modalStepBranchS4Keyed_branch_superset (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ x ∈ b, x ∈ b' := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, -, -⟩ := hsf
    intro b' hb' x hx
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact List.mem_append_right _ hx
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, -, -⟩ := hsf
    intro b' hb' x hx
    simp only [List.mem_map] at hb'
    obtain ⟨br, -, rfl⟩ := hb'
    exact List.mem_append_right _ hx
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, -, -⟩ := hsf
    intro b' hb' x hx
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact List.mem_append_right _ hx
  · rw [hres] at hsf
    simp at hsf

/-- **Ordered-driver form of `modalStepBranchS4Keyed_branch_superset`.** Every branch the
ordered stepper produces is still a superset of the pre-step branch, by the identical
argument: the shared body's output always has the literal shape `X ++ b`, regardless of which
formula was selected or which of the four result shapes fired. Extracted via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction;
the case split on `result` below is otherwise verbatim. -/
lemma modalStepBranchS4KeyedOrdered_branch_superset (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ x ∈ b, x ∈ b' := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, -, -⟩ := hsf
    intro b' hb' x hx
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact List.mem_append_right _ hx
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, -, -⟩ := hsf
    intro b' hb' x hx
    simp only [List.mem_map] at hb'
    obtain ⟨br, -, rfl⟩ := hb'
    exact List.mem_append_right _ hx
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, -, -, -⟩ := hsf
    intro b' hb' x hx
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact List.mem_append_right _ hx
  · rw [hres] at hsf
    simp at hsf

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Reusable result-shape-agnostic `keys'` extraction**: whatever `result` turns out to be
(linear/branching/persistent/notApplicable), the 4th tuple component of
`modalStepBranchS4Keyed`'s inner `match result with ...` is always the SAME local `keysLocal`
term (only the first three components vary by branch). This factors out the "case on `result`,
discard everything but the `keys'` component" boilerplate common to all 9
`sf.sign`/`sf.formula` leaves of `modalStepBranchS4_preserves_keyLowerBd`'s assembly, so that
proof only needs to case on `sf.sign`/`sf.formula` (to pin `keysLocal` itself), never on
`result`. -/
lemma modalStepBranchS4Keyed_result_keys_eq
    (result : RuleResult (Proposition Atom) WorldIndex)
    (newAcc0 : Accessibility)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (keysLocal : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hsf : (match result with
      | .linear nf => some ([nf ++ b], [e ++ [sf]], newAcc0, keysLocal)
      | .branching brs => some (brs.map (· ++ b), brs.map (fun _ => e ++ [sf]), newAcc0, keysLocal)
      | .persistent nf => some ([nf ++ b], [e], newAcc0, keysLocal)
      | .notApplicable => none) = some (newBs, newExps, newAcc, keys')) :
    keys' = keysLocal := by
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.2.symm
  · rw [hres] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.2.symm
  · rw [hres] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.2.symm
  · rw [hres] at hsf; simp at hsf

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Reusable result-shape-agnostic accessibility extraction**, dual of
`modalStepBranchS4Keyed_result_keys_eq`: whatever `result` turns out to be, the 3rd tuple
component of the inner `match result with ...` is always the same `newAcc0`. Needed by
`keysOriginS4`'s preservation at the 12 non-minting shapes, where `result` may be any
of `.linear`/`.branching`/`.persistent` but the accessibility component is uniformly `newAcc0`
regardless. -/
lemma modalStepBranchS4Keyed_result_acc_eq
    (result : RuleResult (Proposition Atom) WorldIndex)
    (newAcc0 : Accessibility)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (keysLocal : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hsf : (match result with
      | .linear nf => some ([nf ++ b], [e ++ [sf]], newAcc0, keysLocal)
      | .branching brs => some (brs.map (· ++ b), brs.map (fun _ => e ++ [sf]), newAcc0, keysLocal)
      | .persistent nf => some ([nf ++ b], [e], newAcc0, keysLocal)
      | .notApplicable => none) = some (newBs, newExps, newAcc, keys')) :
    newAcc = newAcc0 := by
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.1.symm
  · rw [hres] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.1.symm
  · rw [hres] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.1.symm
  · rw [hres] at hsf; simp at hsf

omit [Hashable Atom] in
/-- The T-augmented rule `modalApplyOneT` never mints at its own two relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): `acc` is unchanged and every emitted formula's label is a known world
of `b` -- either the source's own world `w` (self-propagation, known since `sf ∈ b`) or one of
K's own `boxPos`/`diamondNeg` propagation targets (known via `accTargetsKnown`, exactly as in
K's own `modalApplyOne_knownWorlds_step`). Needed as the base layer for the S4-specific composed
dichotomy (`modalApplyOneS4Rules_boxPos_diaNeg_known_S4`), since T's own
`modalApplyOneT_knownWorldsStep` (`TDriver.lean`) is `private` and unavailable across files. -/
private lemma modalApplyOneT_boxPos_diaNeg_known_S4
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneT sf b acc).snd = acc ∧
    (match (modalApplyOneT sf b acc).fst with
      | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
      | .notApplicable => True
      | _ => False) := by
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, w⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hK := modalApplyOne_boxPos_eq
      (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    have hKW := modalApplyOne_knownWorlds_step
      (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
    have hself : ∀ x ∈ modalTBoxSelf b φ w, x.label ∈ modalKnownWorlds b := by
      intro x hx
      simp only [modalTBoxSelf] at hx
      split_ifs at hx with hmem
      · simp at hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact label_mem_modalKnownWorlds
          (sf := (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) hsfmem
    rcases hkeq : modalApplyOne (⟨.pos, .box φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc with ⟨kResult, kAcc⟩
    simp only [hkeq] at hK hKW
    rcases hK with hk | ⟨kForms, hk⟩
    · subst hk
      unfold modalApplyOneT
      simp only [hkeq, apply_ite Prod.snd, apply_ite Prod.fst, ite_self]
      rcases hKW with ⟨hacc, -⟩ | ⟨-, hfalse⟩
      · subst hacc
        refine ⟨rfl, ?_⟩
        split_ifs with hemp
        · trivial
        · exact hself
      · simp at hfalse
    · subst hk
      unfold modalApplyOneT
      simp only [hkeq]
      rcases hKW with ⟨hacc, hmatch⟩ | ⟨-, hfalse⟩
      · subst hacc
        refine ⟨rfl, ?_⟩
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hmatch x hx
        · exact hself x hx
      · simp at hfalse
  · obtain ⟨s, ff, w⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hK := modalApplyOne_diamondNeg_eq
      (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    have hKW := modalApplyOne_knownWorlds_step
      (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
    have hself : ∀ x ∈ modalTDiaNegSelf b φ w, x.label ∈ modalKnownWorlds b := by
      intro x hx
      simp only [modalTDiaNegSelf] at hx
      split_ifs at hx with hmem
      · simp at hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact label_mem_modalKnownWorlds
          (sf := (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) hsfmem
    rcases hkeq : modalApplyOne (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc with ⟨kResult, kAcc⟩
    simp only [hkeq] at hK hKW
    rcases hK with hk | ⟨kForms, hk⟩
    · subst hk
      unfold modalApplyOneT
      simp only [hkeq, apply_ite Prod.snd, apply_ite Prod.fst, ite_self]
      rcases hKW with ⟨hacc, -⟩ | ⟨-, hfalse⟩
      · subst hacc
        refine ⟨rfl, ?_⟩
        split_ifs with hemp
        · trivial
        · exact hself
      · simp at hfalse
    · subst hk
      unfold modalApplyOneT
      simp only [hkeq]
      rcases hKW with ⟨hacc, hmatch⟩ | ⟨-, hfalse⟩
      · subst hacc
        refine ⟨rfl, ?_⟩
        intro x hx
        simp only [List.mem_append, List.mem_filter] at hx
        rcases hx with hx | ⟨hx, -⟩
        · exact hmatch x hx
        · exact hself x hx
      · simp at hfalse

omit [Hashable Atom] in
/-- The S4-augmented rule `modalApplyOneS4Rules` never mints at its two T/4-relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): composes `modalApplyOneT_boxPos_diaNeg_known_S4` (K+T layer) with the
4-rule propagation (`modalFourBoxProp`/`modalFourDiaNegProp`), whose targets are recorded
successors of `w` -- known via `accTargetsKnown` composed with `mem_successorsOf_hasEdge`. -/
private lemma modalApplyOneS4Rules_boxPos_diaNeg_known_S4
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneS4Rules sf b acc).snd = acc ∧
    (match (modalApplyOneS4Rules sf b acc).fst with
      | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
      | .notApplicable => True
      | _ => False) := by
  obtain ⟨hTacc, hT⟩ := modalApplyOneT_boxPos_diaNeg_known_S4 sf b acc hsfmem hknown h
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, w⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hfour : ∀ x ∈ modalFourBoxProp b acc φ w, x.label ∈ modalKnownWorlds b := by
      intro x hx
      unfold modalFourBoxProp at hx
      simp only [List.mem_filterMap] at hx
      obtain ⟨w', hw', hxeq⟩ := hx
      split at hxeq
      · simp at hxeq
      · simp only [Option.some.injEq] at hxeq
        subst hxeq
        exact hknown w w' (mem_successorsOf_hasEdge hw')
    rcases htr : modalApplyOneT (⟨.pos, .box φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc with ⟨tResult, tAcc⟩
    rw [htr] at hTacc hT
    dsimp only at hTacc hT
    unfold modalApplyOneS4Rules
    rw [htr]
    dsimp only
    rcases htres : tResult with tf | tbrs | tf | -
    · rw [htres] at hT; simp at hT
    · rw [htres] at hT; simp at hT
    · rw [htres] at hT
      dsimp only
      refine ⟨hTacc, ?_⟩
      intro x hx
      simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | ⟨hx, -⟩
      · exact hT x hx
      · exact hfour x hx
    · rw [htres] at hT
      simp only [apply_ite Prod.snd, apply_ite Prod.fst, ite_self]
      refine ⟨hTacc, ?_⟩
      split_ifs with hemp
      · trivial
      · exact hfour
  · obtain ⟨s, ff, w⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hfour : ∀ x ∈ modalFourDiaNegProp b acc φ w, x.label ∈ modalKnownWorlds b := by
      intro x hx
      unfold modalFourDiaNegProp at hx
      simp only [List.mem_filterMap] at hx
      obtain ⟨w', hw', hxeq⟩ := hx
      split at hxeq
      · simp at hxeq
      · simp only [Option.some.injEq] at hxeq
        subst hxeq
        exact hknown w w' (mem_successorsOf_hasEdge hw')
    rcases htr : modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc with ⟨tResult, tAcc⟩
    rw [htr] at hTacc hT
    dsimp only at hTacc hT
    unfold modalApplyOneS4Rules
    rw [htr]
    dsimp only
    rcases htres : tResult with tf | tbrs | tf | -
    · rw [htres] at hT; simp at hT
    · rw [htres] at hT; simp at hT
    · rw [htres] at hT
      dsimp only
      refine ⟨hTacc, ?_⟩
      intro x hx
      simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | ⟨hx, -⟩
      · exact hT x hx
      · exact hfour x hx
    · rw [htres] at hT
      simp only [apply_ite Prod.snd, apply_ite Prod.fst, ite_self]
      refine ⟨hTacc, ?_⟩
      split_ifs with hemp
      · trivial
      · exact hfour

omit [Hashable Atom] in
/-- Outside the two K-minting shapes, and with `sf.formula` non-modal (neither `box` nor
`diamond`), `modalApplyOne` never touches `acc` and every emitted formula's label is `sf.label`
(the propositional decomposition rules never leave the source world): the goal reduces to K's
own `tryAllPropRules` dispatch, whose output labels are exactly `sf.label`
(`modalApplyOne_prop_outputs_subset`), or a vacuous `.notApplicable`. -/
private lemma modalApplyOne_nonModal_known_S4
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    (modalApplyOne sf b acc).snd = acc ∧
    (match (modalApplyOne sf b acc).fst with
      | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
      | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
      | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
      | .notApplicable => True) := by
  have hprop := modalApplyOne_prop_outputs_subset sf
  unfold modalApplyOne
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · simp only [hpa, if_true]
    refine ⟨trivial, ?_⟩
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
    rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
      simp_all

/-- **Composite non-mint known-worlds fact for `modalApplyOneS4Keyed`**: at any signed formula
outside the two minting shapes (`F(□φ)@w`, `T(◇φ)@w`), `modalApplyOneS4Keyed` reduces to
`modalApplyOneS4` (its own wildcard branch), which reduces to `modalApplyOneS4Rules` (no guard
outside the minting shapes) -- either at the two T/4-relevant shapes
(`modalApplyOneS4Rules_boxPos_diaNeg_known_S4`) or, combined with the disjointness of the
minting/T4-relevant shape sets, at a genuinely non-modal shape
(`modalApplyOne_nonModal_known_S4`). Every emitted formula's label stays inside
`modalKnownWorlds b`: exactly the fact `keysTotal`'s preservation needs at its 12 non-minting
`sf.sign`/`sf.formula` leaves. -/
lemma modalApplyOneS4Keyed_nonMint_known_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    (match (modalApplyOneS4Keyed φ₀ keys sf b acc).fst with
      | .linear fs => ∀ x ∈ fs, x.label ∈ modalKnownWorlds b
      | .branching brs => ∀ x ∈ brs.flatten, x.label ∈ modalKnownWorlds b
      | .persistent fs => ∀ x ∈ fs, x.label ∈ modalKnownWorlds b
      | .notApplicable => True) := by
  obtain ⟨h1, h2⟩ := h
  have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
    unfold modalApplyOneS4Keyed
    rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
      simp_all
  rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc ⟨h1, h2⟩]
  by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · have hres := (modalApplyOneS4Rules_boxPos_diaNeg_known_S4 sf b acc hsfmem hknown h2').2
    rcases hr : (modalApplyOneS4Rules sf b acc).fst with lf | brs | pf | -
    · rw [hr] at hres; exact hres.elim
    · rw [hr] at hres; exact hres.elim
    · rw [hr] at hres; exact hres
    · rw [hr] at hres; trivial
  · have hnbd : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
    rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd,
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd]
    have hnb : ∀ φ, sf.formula ≠ .box φ := by
      intro φ hfe
      rcases hs : sf.sign with _ | _
      · exact h2' (Or.inl ⟨hs, φ, hfe⟩)
      · exact h1 ⟨hs, φ, hfe⟩
    have hnd : ∀ φ, sf.formula ≠ .diamond φ := by
      intro φ hfe
      rcases hs : sf.sign with _ | _
      · exact h2 ⟨hs, φ, hfe⟩
      · exact h2' (Or.inr ⟨hs, φ, hfe⟩)
    exact (modalApplyOne_nonModal_known_S4 sf b acc hsfmem hnb hnd).2

/-! ## Non-Minting Universe-Membership Composite (groundwork for `bClosure`)

Mirrors the "known-worlds" composite immediately above (`modalApplyOneT_boxPos_diaNeg_known_S4`/
`modalApplyOneS4Rules_boxPos_diaNeg_known_S4`/`modalApplyOne_nonModal_known_S4`/
`modalApplyOneS4Keyed_nonMint_known_S4`), but concludes full `modalUniverseS4 φ₀` membership
(formula-content *and* label) rather than only the label-side `modalKnownWorlds b` fact --
exactly what `bClosure`'s 12 non-minting-shape obligation needs. Built as direct unfoldings
(`modalApplyOne_boxPos_fst_S4`/`modalApplyOne_diamondNeg_fst_S4`) rather than routing through
the abstract `modalApplyOne_boxPos_eq`/`modalApplyOne_knownWorlds_step` (whose persistent
payload is deliberately existentially-quantified for T/B/S5 reuse, so it carries no formula
content) -- K's own public `modalApplyOne_boxPos_outputs_subset`/
`modalApplyOne_diamondNeg_outputs_subset` supply the formula bound directly against the literal
`boxPropagation`/filterMap content. -/

omit [Hashable Atom] in
/-- `modalApplyOne`'s box-positive shape, unfolded directly to its literal `.persistent`/
`.notApplicable` payload (mirrors `modalApplyOne_boxNeg_mint_fst_S4`'s technique, applied to the
non-minting `boxPos` shape instead). -/
private lemma modalApplyOne_boxPos_fst_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = if (boxPropagation b acc φ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (boxPropagation b acc φ w) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  split_ifs <;> rfl

omit [Hashable Atom] in
/-- `modalApplyOne`'s box-positive shape never touches `acc`. -/
lemma modalApplyOne_boxPos_snd_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
      = acc := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  split_ifs <;> rfl

omit [Hashable Atom] in
/-- `modalApplyOne`'s diamond-negative shape, unfolded directly (dual of
`modalApplyOne_boxPos_fst_S4`). -/
private lemma modalApplyOne_diamondNeg_fst_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst
      = if ((acc.successorsOf w).filterMap (fun w' =>
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
            if b.any (· == sf') then none else some sf')).isEmpty
        then RuleResult.notApplicable
        else RuleResult.persistent ((acc.successorsOf w).filterMap (fun w' =>
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
            if b.any (· == sf') then none else some sf')) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_neg]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  split_ifs <;> rfl

omit [Hashable Atom] in
/-- `modalApplyOne`'s diamond-negative shape never touches `acc`. -/
lemma modalApplyOne_diamondNeg_snd_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
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
/-- **T-augmented universe-membership composite**: at the two T-relevant shapes (`T(□φ)@w`,
`F(◇φ)@w`), `modalApplyOneT` never touches `acc`, and every emitted formula lands in
`modalUniverseS4 φ₀` given the branch invariant `hb` -- combining K's own output-subset facts
(formula bound, via `modalApplyOne_boxPos_outputs_subset`/`modalApplyOne_diamondNeg_outputs_subset`)
with `accTargetsKnown` (label bound on K's propagation targets) and `hb` directly (label bound
on the T-self output, at the unchanged source world). -/
private lemma modalApplyOneT_boxPos_diaNeg_universe_S4
    (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneT sf b acc).snd = acc ∧
    (match (modalApplyOneT sf b acc).fst with
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverseS4 φ₀
      | .notApplicable => True
      | _ => False) := by
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, w⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hsrc : (Proposition.box φ) ∈ modalSubfmls φ₀ :=
      modalUniverseS4_mem_formula (hb _ hsfmem)
    have hKmem : ∀ x ∈ boxPropagation b acc φ w, x ∈ modalUniverseS4 φ₀ := by
      intro x hx
      obtain ⟨hxf, hxl⟩ := modalApplyOne_boxPos_outputs_subset b acc φ w x hx
      have hxlk : x.label ∈ modalKnownWorlds b :=
        hknown w x.label (mem_successorsOf_hasEdge hxl)
      obtain ⟨sf', hsf'mem, hsf'lab⟩ := (mem_modalKnownWorlds b x.label).mp hxlk
      have hbound : sf'.label ≤ modalWorldBoundS4 φ₀ := modalUniverseS4_mem_label (hb sf' hsf'mem)
      rw [hsf'lab] at hbound
      exact mem_modalUniverseS4_of' hbound (modalSubfmls_trans hxf hsrc)
    have hself : ∀ x ∈ modalTBoxSelf b φ w, x ∈ modalUniverseS4 φ₀ := by
      intro x hx
      simp only [modalTBoxSelf] at hx
      split_ifs at hx with hmem
      · simp at hx
      · simp only [List.mem_singleton] at hx
        subst hx
        have hbound : w ≤ modalWorldBoundS4 φ₀ := by
          have := modalUniverseS4_mem_label (hb _ hsfmem)
          simpa using this
        exact mem_modalUniverseS4_of' hbound (modalSubfmls_trans (by simp [modalSubfmls]) hsrc)
    rcases hkeq : modalApplyOne (⟨.pos, .box φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc with ⟨kResult, kAcc⟩
    have hkResult : kResult =
        if (boxPropagation b acc φ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (boxPropagation b acc φ w) := by
      have hfst := modalApplyOne_boxPos_fst_S4 b acc φ w
      rw [hkeq] at hfst
      exact hfst
    have hkAcc : kAcc = acc := by
      have hsnd := modalApplyOne_boxPos_snd_S4 b acc φ w
      rw [hkeq] at hsnd
      exact hsnd
    unfold modalApplyOneT
    simp only [hkeq]
    by_cases hemp : (boxPropagation b acc φ w).isEmpty
    · rw [hkResult, if_pos hemp]
      dsimp only
      split_ifs with hemp2
      · exact ⟨hkAcc, trivial⟩
      · exact ⟨hkAcc, hself⟩
    · rw [hkResult, if_neg hemp]
      dsimp only
      refine ⟨hkAcc, ?_⟩
      intro x hx
      simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | ⟨hx, -⟩
      · exact hKmem x hx
      · exact hself x hx
  · obtain ⟨s, ff, w⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ₀ :=
      modalUniverseS4_mem_formula (hb _ hsfmem)
    have hKmem : ∀ x ∈ (acc.successorsOf w).filterMap (fun w' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf') then none else some sf'), x ∈ modalUniverseS4 φ₀ := by
      intro x hx
      obtain ⟨hxf, hxl⟩ := modalApplyOne_diamondNeg_outputs_subset b acc φ w x hx
      have hxlk : x.label ∈ modalKnownWorlds b :=
        hknown w x.label (mem_successorsOf_hasEdge hxl)
      obtain ⟨sf', hsf'mem, hsf'lab⟩ := (mem_modalKnownWorlds b x.label).mp hxlk
      have hbound : sf'.label ≤ modalWorldBoundS4 φ₀ := modalUniverseS4_mem_label (hb sf' hsf'mem)
      rw [hsf'lab] at hbound
      exact mem_modalUniverseS4_of' hbound (modalSubfmls_trans hxf hsrc)
    have hself : ∀ x ∈ modalTDiaNegSelf b φ w, x ∈ modalUniverseS4 φ₀ := by
      intro x hx
      simp only [modalTDiaNegSelf] at hx
      split_ifs at hx with hmem
      · simp at hx
      · simp only [List.mem_singleton] at hx
        subst hx
        have hbound : w ≤ modalWorldBoundS4 φ₀ := by
          have := modalUniverseS4_mem_label (hb _ hsfmem)
          simpa using this
        exact mem_modalUniverseS4_of' hbound (modalSubfmls_trans (by simp [modalSubfmls]) hsrc)
    rcases hkeq : modalApplyOne (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc with ⟨kResult, kAcc⟩
    have hkResult : kResult =
        if ((acc.successorsOf w).filterMap (fun w' =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
              if b.any (· == sf') then none else some sf')).isEmpty
          then RuleResult.notApplicable
          else RuleResult.persistent ((acc.successorsOf w).filterMap (fun w' =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
              if b.any (· == sf') then none else some sf')) := by
      have hfst := modalApplyOne_diamondNeg_fst_S4 b acc φ w
      rw [hkeq] at hfst
      exact hfst
    have hkAcc : kAcc = acc := by
      have hsnd := modalApplyOne_diamondNeg_snd_S4 b acc φ w
      rw [hkeq] at hsnd
      exact hsnd
    unfold modalApplyOneT
    simp only [hkeq]
    by_cases hemp : ((acc.successorsOf w).filterMap (fun w' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf') then none else some sf')).isEmpty
    · rw [hkResult, if_pos hemp]
      dsimp only
      split_ifs with hemp2
      · exact ⟨hkAcc, trivial⟩
      · exact ⟨hkAcc, hself⟩
    · rw [hkResult, if_neg hemp]
      dsimp only
      refine ⟨hkAcc, ?_⟩
      intro x hx
      simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | ⟨hx, -⟩
      · exact hKmem x hx
      · exact hself x hx

omit [Hashable Atom] in
/-- **S4-augmented universe-membership composite**: composes
`modalApplyOneT_boxPos_diaNeg_universe_S4` (K+T layer) with the 4-rule propagation
(`modalFourBoxProp`/`modalFourDiaNegProp`), whose targets are recorded successors of `w` (known
via `accTargetsKnown`) and whose formula-content is `sf.formula` itself (self-membership via
`modalSubfmls_self_mem`). -/
private lemma modalApplyOneS4Rules_boxPos_diaNeg_universe_S4
    (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneS4Rules sf b acc).snd = acc ∧
    (match (modalApplyOneS4Rules sf b acc).fst with
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverseS4 φ₀
      | .notApplicable => True
      | _ => False) := by
  obtain ⟨hTacc, hT⟩ := modalApplyOneT_boxPos_diaNeg_universe_S4 φ₀ sf b acc hb hsfmem hknown h
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, w⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hsrc : (Proposition.box φ) ∈ modalSubfmls φ₀ :=
      modalUniverseS4_mem_formula (hb _ hsfmem)
    have hfour : ∀ x ∈ modalFourBoxProp b acc φ w, x ∈ modalUniverseS4 φ₀ := by
      intro x hx
      unfold modalFourBoxProp at hx
      simp only [List.mem_filterMap] at hx
      obtain ⟨w', hw', hxeq⟩ := hx
      split at hxeq
      · simp at hxeq
      · simp only [Option.some.injEq] at hxeq
        subst hxeq
        have hxlk : w' ∈ modalKnownWorlds b := hknown w w' (mem_successorsOf_hasEdge hw')
        obtain ⟨sf', hsf'mem, hsf'lab⟩ := (mem_modalKnownWorlds b w').mp hxlk
        have hbound : sf'.label ≤ modalWorldBoundS4 φ₀ :=
          modalUniverseS4_mem_label (hb sf' hsf'mem)
        rw [hsf'lab] at hbound
        exact mem_modalUniverseS4_of' hbound hsrc
    rcases htr : modalApplyOneT (⟨.pos, .box φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc with ⟨tResult, tAcc⟩
    rw [htr] at hTacc hT
    dsimp only at hTacc hT
    unfold modalApplyOneS4Rules
    rw [htr]
    dsimp only
    rcases htres : tResult with tf | tbrs | tf | -
    · rw [htres] at hT; simp at hT
    · rw [htres] at hT; simp at hT
    · rw [htres] at hT
      dsimp only
      refine ⟨hTacc, ?_⟩
      intro x hx
      simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | ⟨hx, -⟩
      · exact hT x hx
      · exact hfour x hx
    · rw [htres] at hT
      simp only [apply_ite Prod.snd, apply_ite Prod.fst, ite_self]
      refine ⟨hTacc, ?_⟩
      split_ifs with hemp
      · trivial
      · exact hfour
  · obtain ⟨s, ff, w⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ₀ :=
      modalUniverseS4_mem_formula (hb _ hsfmem)
    have hfour : ∀ x ∈ modalFourDiaNegProp b acc φ w, x ∈ modalUniverseS4 φ₀ := by
      intro x hx
      unfold modalFourDiaNegProp at hx
      simp only [List.mem_filterMap] at hx
      obtain ⟨w', hw', hxeq⟩ := hx
      split at hxeq
      · simp at hxeq
      · simp only [Option.some.injEq] at hxeq
        subst hxeq
        have hxlk : w' ∈ modalKnownWorlds b := hknown w w' (mem_successorsOf_hasEdge hw')
        obtain ⟨sf', hsf'mem, hsf'lab⟩ := (mem_modalKnownWorlds b w').mp hxlk
        have hbound : sf'.label ≤ modalWorldBoundS4 φ₀ :=
          modalUniverseS4_mem_label (hb sf' hsf'mem)
        rw [hsf'lab] at hbound
        exact mem_modalUniverseS4_of' hbound hsrc
    rcases htr : modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc with ⟨tResult, tAcc⟩
    rw [htr] at hTacc hT
    dsimp only at hTacc hT
    unfold modalApplyOneS4Rules
    rw [htr]
    dsimp only
    rcases htres : tResult with tf | tbrs | tf | -
    · rw [htres] at hT; simp at hT
    · rw [htres] at hT; simp at hT
    · rw [htres] at hT
      dsimp only
      refine ⟨hTacc, ?_⟩
      intro x hx
      simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | ⟨hx, -⟩
      · exact hT x hx
      · exact hfour x hx
    · rw [htres] at hT
      simp only [apply_ite Prod.snd, apply_ite Prod.fst, ite_self]
      refine ⟨hTacc, ?_⟩
      split_ifs with hemp
      · trivial
      · exact hfour

omit [Hashable Atom] in
/-- Outside the two K-minting shapes, and with `sf.formula` non-modal, every emitted formula
lands in `modalUniverseS4 φ₀`: `modalApplyOne_prop_outputs_subset` gives formula ∈
`modalSubfmls sf.formula` at the unchanged label `sf.label`, composed with `hb`'s own bound on
`sf` via `modalSubfmls_trans`. Universe-membership analog of
`modalApplyOne_nonModal_known_S4`. -/
private lemma modalApplyOne_nonModal_universe_S4
    (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsfmem : sf ∈ b)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    (modalApplyOne sf b acc).snd = acc ∧
    (match (modalApplyOne sf b acc).fst with
      | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverseS4 φ₀
      | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverseS4 φ₀
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverseS4 φ₀
      | .notApplicable => True) := by
  have hprop := modalApplyOne_prop_outputs_subset sf
  have hsfbound : sf ∈ modalUniverseS4 φ₀ := hb sf hsfmem
  unfold modalApplyOne
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · simp only [hpa, if_true]
    refine ⟨trivial, ?_⟩
    rcases hpr : tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
      formulas | branches | formulas | -
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzf, hzlabel⟩ := hprop z hz
      exact mem_modalUniverseS4_of' (hzlabel ▸ modalUniverseS4_mem_label hsfbound)
        (modalSubfmls_trans hzf (modalUniverseS4_mem_formula hsfbound))
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzf, hzlabel⟩ := hprop z hz
      exact mem_modalUniverseS4_of' (hzlabel ▸ modalUniverseS4_mem_label hsfbound)
        (modalSubfmls_trans hzf (modalUniverseS4_mem_formula hsfbound))
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzf, hzlabel⟩ := hprop z hz
      exact mem_modalUniverseS4_of' (hzlabel ▸ modalUniverseS4_mem_label hsfbound)
        (modalSubfmls_trans hzf (modalUniverseS4_mem_formula hsfbound))
    · rw [hpr] at hpa; simp [RuleResult.isApplicable] at hpa
  · rw [if_neg hpa]
    rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
      simp_all

/-- **Composite non-mint universe-membership fact for `modalApplyOneS4Keyed`**: at any signed
formula outside the two minting shapes, every emitted formula lands in `modalUniverseS4 φ₀`.
Universe-membership analog of `modalApplyOneS4Keyed_nonMint_known_S4`, exactly the fact
`bClosure`'s preservation needs at its 12 non-minting `sf.sign`/`sf.formula` leaves. -/
lemma modalApplyOneS4Keyed_nonMint_universe_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    (match (modalApplyOneS4Keyed φ₀ keys sf b acc).fst with
      | .linear fs => ∀ x ∈ fs, x ∈ modalUniverseS4 φ₀
      | .branching brs => ∀ x ∈ brs.flatten, x ∈ modalUniverseS4 φ₀
      | .persistent fs => ∀ x ∈ fs, x ∈ modalUniverseS4 φ₀
      | .notApplicable => True) := by
  obtain ⟨h1, h2⟩ := h
  have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
    unfold modalApplyOneS4Keyed
    rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
      simp_all
  rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc ⟨h1, h2⟩]
  by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · have hres := (modalApplyOneS4Rules_boxPos_diaNeg_universe_S4 φ₀ sf b acc hb hsfmem hknown
      h2').2
    rcases hr : (modalApplyOneS4Rules sf b acc).fst with lf | brs | pf | -
    · rw [hr] at hres; exact hres.elim
    · rw [hr] at hres; exact hres.elim
    · rw [hr] at hres; exact hres
    · rw [hr] at hres; trivial
  · have hnbd : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
    rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd,
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd]
    have hnb : ∀ φ, sf.formula ≠ .box φ := by
      intro φ hfe
      rcases hs : sf.sign with _ | _
      · exact h2' (Or.inl ⟨hs, φ, hfe⟩)
      · exact h1 ⟨hs, φ, hfe⟩
    have hnd : ∀ φ, sf.formula ≠ .diamond φ := by
      intro φ hfe
      rcases hs : sf.sign with _ | _
      · exact h2 ⟨hs, φ, hfe⟩
      · exact h2' (Or.inr ⟨hs, φ, hfe⟩)
    exact (modalApplyOne_nonModal_universe_S4 φ₀ sf b acc hb hsfmem hnb hnd).2

/-- Every key threaded through `modalStepBranchS4Keyed` survives as a step: `keys' = keys` (the
12 non-minting leaves) or `keys' = keys ++ [newEntry]` (the two minting leaves' unblocked case),
so `keys ⊆ keys'` always. Needed for `keysTotal`'s preservation to lift OLD known worlds' keys
forward. -/
lemma modalStepBranchS4Keyed_keys_subset
    (φ₀ : Proposition Atom) (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    keys ⊆ keys' := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  rw [hkeq]
  intro p hp
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only []
  all_goals first
    | exact hp
    | skip
  case neg.neg.box =>
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · exact List.mem_append_left _ hp
    · exact hp
  case neg.pos.diamond =>
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · exact List.mem_append_left _ hp
    · exact hp

/-- **Ordered-driver form of `modalStepBranchS4Keyed_keys_subset`.** `keys ⊆ keys'` still holds
for the ordered stepper, by the identical argument: the selected formula's own effect on `keys'`
is `keys' = keys` (12 leaves) or `keys' = keys ++ [newEntry]` (2 minting leaves), regardless of
which formula in `b` was chosen. -/
lemma modalStepBranchS4KeyedOrdered_keys_subset
    (φ₀ : Proposition Atom) (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    keys ⊆ keys' := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  rw [hkeq]
  intro p hp
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only []
  all_goals first
    | exact hp
    | skip
  case neg.box =>
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · exact List.mem_append_left _ hp
    · exact hp
  case pos.diamond =>
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · exact List.mem_append_left _ hp
    · exact hp

/-- **Composite `.snd = acc` fact for `modalApplyOneS4Keyed`'s 12 non-minting leaves**: mirrors
`modalApplyOneS4Keyed_nonMint_known_S4`'s exact case-split (same three underlying pieces --
`modalApplyOneS4Rules_boxPos_diaNeg_known_S4`/`modalApplyOne_nonModal_known_S4`, both of which
also supply `.snd = acc`), extracting the accessibility-unchanged half instead of the
known-worlds half. Needed for `accFresh`/`accKnown`'s preservation at the 12
non-minting shapes: `acc` is untouched there, so those two invariants (neither of which depends on
`e`/`b` beyond `acc` itself, or trivially so) carry over for free. -/
lemma modalApplyOneS4Keyed_nonMint_snd_eq_acc
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneS4Keyed φ₀ keys sf b acc).snd = acc := by
  obtain ⟨h1, h2⟩ := h
  have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
    unfold modalApplyOneS4Keyed
    rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
      simp_all
  rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc ⟨h1, h2⟩]
  by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · exact (modalApplyOneS4Rules_boxPos_diaNeg_known_S4 sf b acc hsfmem hknown h2').1
  · have hnbd : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
    rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd,
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd]
    have hnb : ∀ φ, sf.formula ≠ .box φ := by
      intro φ hfe
      rcases hs : sf.sign with _ | _
      · exact h2' (Or.inl ⟨hs, φ, hfe⟩)
      · exact h1 ⟨hs, φ, hfe⟩
    have hnd : ∀ φ, sf.formula ≠ .diamond φ := by
      intro φ hfe
      rcases hs : sf.sign with _ | _
      · exact h2 ⟨hs, φ, hfe⟩
      · exact h2' (Or.inr ⟨hs, φ, hfe⟩)
    exact (modalApplyOne_nonModal_known_S4 sf b acc hsfmem hnb hnd).1

/-- The keyed S4 fuel-based expansion of a list of branches: `modalExpandBranchesGen`
(`Saturation.lean:201-243`), copy-and-threaded with a fourth `keyss` worklist column carrying
each pending/done branch's own `keys` list (`modalStepBranchS4Keyed`'s threaded birth-key state),
and stepped by the keyed stepper `modalStepBranchS4Keyed φ₀` in place of a fixed
`modalStepBranchGen apply`. At `fuel = 0`, mirrors the generic driver exactly (keys play no role
in the base case, since it only inspects `branches`/`accs`). At `fuel = fuel' + 1`, the inner
`processNext` recursion threads `keys` through every arm identically to how it threads `accs`:
closed branches carry their `keys` to `done` unchanged; a saturated (`none`) branch returns
`.openBranch` exactly as before (its `keys` value is not part of `ModalTableauResult`, per
Decision D2 in the module docstring below -- only `(b, acc)` are returned, matching every other
driver's `ModalTableauResult`); an expanded branch replicates the single returned `keys'` across
every one of `newBs`' children (matching `modalStepBranchS4Keyed`'s `.branching` arm, which
produces the SAME `keys'` for every branch it splits into). -/
def modalExpandBranchesS4Keyed
    (φ₀ : Proposition Atom)
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
    (fuel : Nat) : ModalTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Fuel exhausted: return first open branch with its local accessibility relation
    -- (mirrors `modalExpandBranchesGen`'s base case exactly; `keyss` plays no role here,
    -- since `ModalTableauResult` never carries `keys`).
    match (branches.zip accs) |>.findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | some (b, a) => .openBranch b a
    | none => .closed
  | fuel' + 1 =>
    -- processNext: iterate through branches, finding the first open one to expand, threading
    -- `keys` alongside `acc` for every entry.
    let rec @[nolint docBlame] processNext
        (pending : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        : ModalTableauResult Atom :=
      match pending, pendingExp, pendingAccs, pendingKeys with
      | [], _, _, _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs, a :: restAs, k :: restKs =>
        if isModalClosed b then
          -- Branch is closed: skip it, carry its acc/keys to done
          processNext restBs restEs restAs restKs (done ++ [b]) (doneExp ++ [e]) (doneAccs ++ [a])
            (doneKeys ++ [k])
        else
          match modalStepBranchS4Keyed φ₀ b e a k with
          | none =>
            -- Branch is saturated and open: return with this branch's local acc
            .openBranch b a
          | some (newBs, newExps, newAcc, keys') =>
            -- Expanded: recurse with new branches using newAcc/keys' for each child
            modalExpandBranchesS4Keyed φ₀
              (done ++ newBs ++ restBs)
              (doneExp ++ newExps ++ restEs)
              (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              (doneKeys ++ List.replicate newBs.length keys' ++ restKs)
              fuel'
      | _, _, _, _ => .closed  -- malformed (length invariant rules this out)
    processNext branches expandedSets accs keyss [] [] [] []

/-! ## `RuleApplySt` Bridge for the Keyed S4 Driver

The `RuleApplySt` ladder's first real consumer: `modalApplyOneS4KeyedSt` below is the
`RuleApplySt Atom (List (WorldIndex × Finset (Sign × Proposition Atom)))` instantiation of the
keyed S4 rule, and the four theorems that follow bridge it, through the generic state-threaded
driver (`modalStepBranchGenSt`/`modalExpandBranchesGenSt`, `Saturation.lean`), onto the bespoke
keyed driver (`modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed`) defined above. This section
is purely additive: none of `modalApplyOneS4Keyed`, `modalStepBranchS4Keyed`,
`modalStepBranchS4KeyedBody`, `modalStepBranchS4KeyedOrdered`, or `modalExpandBranchesS4Keyed` is
redefined. -/

/-- **State-threaded keyed S4 stepper.** The `RuleApplySt` instantiation for the keyed S4 driver:
threads the birth-key list `keys` explicitly through the rule's own signature instead of
`modalApplyOneS4Keyed` re-deriving it from `blockingWorldS4Keyed`'s stateless computation site by
site. Makes the `blockingWorldS4Keyed` blocking decision ONCE per call, at the two minting shapes
(`.neg, □φ` and `.pos, ◇φ`); all other shapes fall through to `modalApplyOneS4` unchanged. -/
def modalApplyOneS4KeyedSt (φ₀ : Proposition Atom) :
    RuleApplySt Atom (List (WorldIndex × Finset (Sign × Proposition Atom))) :=
  fun sf b acc keys =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock, keys)
      | none =>
        ((modalApplyOneS4KeyedMint sf b acc).1, (modalApplyOneS4KeyedMint sf b acc).2,
          keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)])
    | .pos, .diamond φ =>
      match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock, keys)
      | none =>
        ((modalApplyOneS4KeyedMint sf b acc).1, (modalApplyOneS4KeyedMint sf b acc).2,
          keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)])
    | _, _ => ((modalApplyOneS4 φ₀ sf b acc).1, (modalApplyOneS4 φ₀ sf b acc).2, keys)

/-- **Projection bridge.** The state-threaded rule's `(RuleResult, Accessibility)` projection
equals the output of the stateless `modalApplyOneS4Keyed` at the same arguments -- the
state-threading is invisible to the first two components. -/
theorem modalApplyOneS4KeyedSt_proj (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    ((modalApplyOneS4KeyedSt φ₀ sf b acc keys).1,
       (modalApplyOneS4KeyedSt φ₀ sf b acc keys).2.1)
      = modalApplyOneS4Keyed φ₀ keys sf b acc := by
  unfold modalApplyOneS4KeyedSt modalApplyOneS4Keyed
  rcases sf with ⟨s, f, w⟩
  cases s <;> cases f <;>
    simp_all <;>
    (try split) <;> simp_all

/-- **Componentwise equation.** `modalApplyOneS4KeyedSt` is definitionally the stateless
`modalApplyOneS4Keyed`'s `(RuleResult, Accessibility)` pair, paired with the same `keys'`
expression the bespoke stepper `modalStepBranchS4Keyed` computes inline at each minting shape.
This is the key lemma bridging the state-threaded and stateless keyed rules: it identifies the
state-threaded rule's third component with the exact `keys'` term the ladder needs to
reconstruct. -/
theorem modalApplyOneS4KeyedSt_eq (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    modalApplyOneS4KeyedSt φ₀ sf b acc keys =
      ((modalApplyOneS4Keyed φ₀ keys sf b acc).1, (modalApplyOneS4Keyed φ₀ keys sf b acc).2,
        (match sf.sign, sf.formula with
          | .neg, .box φ =>
            match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
            | some _ => keys
            | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .neg φ sf.label)]
          | .pos, .diamond φ =>
            match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
            | some _ => keys
            | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b .pos φ sf.label)]
          | _, _ => keys)) := by
  unfold modalApplyOneS4KeyedSt modalApplyOneS4Keyed
  rcases sf with ⟨s, f, w⟩
  cases s <;> cases f <;> dsimp only <;>
    (split <;> rename_i h <;> simp only [h])

/-- **Generic stepper instantiation.** The state-threaded generic branch stepper
`modalStepBranchGenSt`, instantiated at `modalApplyOneS4KeyedSt φ₀`, computes exactly the bespoke
keyed stepper `modalStepBranchS4Keyed φ₀` -- the `RuleApplySt` ladder's generic per-branch step
machinery is interchangeable with the hand-written keyed driver at every input. -/
theorem modalStepBranchGenSt_eq_S4Keyed (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) :
    modalStepBranchGenSt (modalApplyOneS4KeyedSt φ₀) b e acc keys
      = modalStepBranchS4Keyed φ₀ b e acc keys := by
  unfold modalStepBranchGenSt modalStepBranchS4Keyed
  congr 1
  funext sf
  by_cases hexp : e.any (· == sf)
  · simp [hexp]
  · simp only [hexp, Bool.false_eq_true, if_false]
    rw [modalApplyOneS4KeyedSt_eq]
    rfl

/-- **Generic loop instantiation (entry-point bridge).** The state-threaded generic fuel-based
expansion loop `modalExpandBranchesGenSt`, instantiated at `modalApplyOneS4KeyedSt φ₀`, computes
exactly the bespoke keyed loop `modalExpandBranchesS4Keyed φ₀` at every fuel value -- the
`RuleApplySt` ladder's first genuine consumer, making `modalExpandBranchesS4Keyed` reachable
through the generic driver rather than only through its own bespoke copy-and-thread
implementation. -/
theorem modalExpandBranchesGenSt_eq_S4Keyed (φ₀ : Proposition Atom)
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
    (fuel : Nat) :
    modalExpandBranchesGenSt (modalApplyOneS4KeyedSt φ₀) branches expandedSets accs keyss fuel
      = modalExpandBranchesS4Keyed φ₀ branches expandedSets accs keyss fuel := by
  induction fuel generalizing branches expandedSets accs keyss with
  | zero => simp only [modalExpandBranchesGenSt, modalExpandBranchesS4Keyed]; rfl
  | succ fuel' ih =>
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        modalExpandBranchesGenSt.processNext (modalApplyOneS4KeyedSt φ₀) fuel' pending pendingExp
            pendingAccs pendingKeys done doneExp doneAccs doneKeys =
          modalExpandBranchesS4Keyed.processNext φ₀ fuel' pending pendingExp pendingAccs
            pendingKeys done doneExp doneAccs doneKeys by
      have hkey := key branches expandedSets accs keyss [] [] [] []
      simpa [modalExpandBranchesGenSt, modalExpandBranchesS4Keyed] using hkey
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
      simp [modalExpandBranchesGenSt.processNext, modalExpandBranchesS4Keyed.processNext]
    | cons b restBs ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
      cases pendingExp with
      | nil => simp [modalExpandBranchesGenSt.processNext, modalExpandBranchesS4Keyed.processNext]
      | cons e restEs =>
        cases pendingAccs with
        | nil => simp [modalExpandBranchesGenSt.processNext, modalExpandBranchesS4Keyed.processNext]
        | cons a restAs =>
          cases pendingKeys with
          | nil =>
            simp [modalExpandBranchesGenSt.processNext, modalExpandBranchesS4Keyed.processNext]
          | cons k restKs =>
            simp only [modalExpandBranchesGenSt.processNext,
              modalExpandBranchesS4Keyed.processNext]
            by_cases hc : isModalClosed b
            · simp only [hc, if_true]
              exact ih_inner restEs restAs restKs (done ++ [b]) (doneExp ++ [e])
                (doneAccs ++ [a]) (doneKeys ++ [k])
            · simp only [hc, Bool.false_eq_true, if_false]
              rw [modalStepBranchGenSt_eq_S4Keyed]
              cases hs : modalStepBranchS4Keyed φ₀ b e a k with
              | none => rfl
              | some x =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := x
                exact ih (done ++ newBs ++ restBs) (doneExp ++ newExps ++ restEs)
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                  (doneKeys ++ List.replicate newBs.length keys' ++ restKs)

/-- The ordered-stepper analogue of `modalExpandBranchesS4Keyed`: identical `processNext`
worklist shape and `keys` threading via `keyss`, with `modalStepBranchS4KeyedOrdered φ₀` stepping
each open branch in place of `modalStepBranchS4Keyed φ₀`. At `fuel = 0`, mirrors the base case of
`modalExpandBranchesS4Keyed` exactly (`keyss` again plays no role, since `ModalTableauResult`
never carries `keys`). At `fuel = fuel' + 1`, `processNext` closes/expands branches identically to
its predecessor, threading `keys'` across every one of a `.branching` split's children exactly as
before. Successor to `modalExpandBranchesS4Keyed`, which Phase 15 retires once this driver has a
proved soundness/completeness pair of its own. -/
def modalExpandBranchesS4KeyedOrdered
    (φ₀ : Proposition Atom)
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility)
    (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
    (fuel : Nat) : ModalTableauResult Atom :=
  match fuel with
  | 0 =>
    -- Fuel exhausted: return first open branch with its local accessibility relation
    -- (mirrors `modalExpandBranchesS4Keyed`'s base case exactly).
    match (branches.zip accs) |>.findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | some (b, a) => .openBranch b a
    | none => .closed
  | fuel' + 1 =>
    -- processNext: iterate through branches, finding the first open one to expand, threading
    -- `keys` alongside `acc` for every entry -- identical shape to
    -- `modalExpandBranchesS4Keyed`'s `processNext`, with the ordered stepper substituted at the
    -- single per-branch call site below.
    let rec @[nolint docBlame] processNext
        (pending : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        : ModalTableauResult Atom :=
      match pending, pendingExp, pendingAccs, pendingKeys with
      | [], _, _, _ => .closed  -- All branches closed
      | b :: restBs, e :: restEs, a :: restAs, k :: restKs =>
        if isModalClosed b then
          -- Branch is closed: skip it, carry its acc/keys to done
          processNext restBs restEs restAs restKs (done ++ [b]) (doneExp ++ [e]) (doneAccs ++ [a])
            (doneKeys ++ [k])
        else
          match modalStepBranchS4KeyedOrdered φ₀ b e a k with
          | none =>
            -- Branch is saturated and open: return with this branch's local acc
            .openBranch b a
          | some (newBs, newExps, newAcc, keys') =>
            -- Expanded: recurse with new branches using newAcc/keys' for each child
            modalExpandBranchesS4KeyedOrdered φ₀
              (done ++ newBs ++ restBs)
              (doneExp ++ newExps ++ restEs)
              (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              (doneKeys ++ List.replicate newBs.length keys' ++ restKs)
              fuel'
      | _, _, _, _ => .closed  -- malformed (length invariant rules this out)
    processNext branches expandedSets accs keyss [] [] [] []

/-- **F8 discharge for `modalApplyOneS4Keyed`** (local shape invariance): outside the two
minting shapes (`F(□φ)@w`/`T(◇φ)@w`, both signs excluded by `hnb`/`hnd`),
`modalApplyOneS4Keyed` reduces to raw `modalApplyOne` regardless of `keys` -- the dispatch chain
`modalApplyOneS4Keyed → modalApplyOneS4 → modalApplyOneS4Rules → modalApplyOneT → modalApplyOne`
fires its catch-all arm at every layer, since `φ` is neither box- nor diamond-shaped -- so K's
own `modalApplyOne_fst_eq_of_not_box` transports directly. Mirrors
`modalApplyOneT_localShapeInvariance` (`TDriver.lean:734`), two layers deeper. -/
lemma modalApplyOneS4Keyed_fst_eq_of_not_box (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) :
    (modalApplyOneS4Keyed φ₀ keys ⟨s, φ, w⟩ b acc).1 =
      (modalApplyOneS4Keyed φ₀ keys ⟨s, φ, w⟩ b' acc').1 := by
  have hred : ∀ (bb : List (SignedFormula (Proposition Atom) WorldIndex)) (ac : Accessibility),
      modalApplyOneS4Keyed φ₀ keys (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        bb ac = modalApplyOne (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) bb ac := by
    intro bb ac
    have heqS4 : modalApplyOneS4Keyed φ₀ keys
        (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) bb ac
        = modalApplyOneS4 φ₀ (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) bb ac := by
      unfold modalApplyOneS4Keyed
      rcases hs : s with _ | _ <;> rcases hf : φ with _ | _ | _ | _ | _ | ψ | ψ <;> simp_all
    rw [heqS4]
    have hnbd1 : ¬ ((⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).sign = .neg ∧
        ∃ ψ, (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).formula = .box ψ) ∧
        ¬ ((⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).sign = .pos ∧
        ∃ ψ, (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).formula = .diamond ψ) :=
      ⟨fun ⟨_, ψ, hfe⟩ => hnb ψ hfe, fun ⟨_, ψ, hfe⟩ => hnd ψ hfe⟩
    rw [modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ bb ac hnbd1]
    have hnbd2 : ¬ ((⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).sign = .pos ∧
        ∃ ψ, (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).formula = .box ψ) ∧
        ¬ ((⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).sign = .neg ∧
        ∃ ψ, (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).formula = .diamond ψ) :=
      ⟨fun ⟨_, ψ, hfe⟩ => hnb ψ hfe, fun ⟨_, ψ, hfe⟩ => hnd ψ hfe⟩
    rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg _ bb ac hnbd2,
        modalApplyOneT_eq_of_not_boxPos_diaNeg _ bb ac hnbd2]
  rw [hred b acc, hred b' acc']
  exact modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'

omit [Hashable Atom] in
/-- `modalApplyOneT`'s accessibility output is always exactly K's own: every match arm in
`modalApplyOneT`'s definition returns the pair's second component unchanged from
`(modalApplyOne sf b acc).snd` (the T self-propagation arms only ever touch the `.fst`
formula-output component). -/
private lemma modalApplyOneT_snd_eq (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneT sf b acc).snd = (modalApplyOne sf b acc).snd := by
  unfold modalApplyOneT
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    first
      | rfl
      | (rcases hk : (modalApplyOne sf b acc) with ⟨kResult, kAcc⟩
         dsimp only
         rcases kResult with kf | kbrs | kf | _ <;> (try split_ifs) <;> rfl)

omit [Hashable Atom] in
/-- `modalApplyOneS4Rules`'s accessibility output is always exactly K's own, one layer up: the
4-rule propagation arms only ever touch the `.fst` formula-output component. -/
lemma modalApplyOneS4Rules_snd_eq (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneS4Rules sf b acc).snd = (modalApplyOne sf b acc).snd := by
  unfold modalApplyOneS4Rules
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    first
      | exact modalApplyOneT_snd_eq sf b acc
      | (rcases ht : (modalApplyOneT sf b acc) with ⟨tResult, tAcc⟩
         have hTA : tAcc = (modalApplyOne sf b acc).snd :=
           (congrArg Prod.snd ht).symm.trans (modalApplyOneT_snd_eq sf b acc)
         dsimp only
         rcases tResult with tf | tbrs | tf | _ <;> (try split_ifs) <;> exact hTA)

/-- **Accessibility-edge monotonicity for `modalApplyOneS4Keyed`**: an existing edge survives
one rule application, for any `keys`. At the two minting shapes, either blocked (a fresh
`addEdge`, surviving by `hasEdge_addEdge_mono`) or unblocked (reduces to raw
`modalApplyOne`, `K`'s own `modalApplyOne_fresh_local` dichotomy applies); at every other shape,
`modalApplyOneS4Keyed` reduces to `modalApplyOneS4Rules` (`heq1`-style, mirroring
`modalApplyOneS4Keyed_nonMint_universe_S4`), whose accessibility output is unconditionally K's
own (`modalApplyOneS4Rules_snd_eq`). Needed for the witness-permanence fields of
`S4KeyedHintikkaInv` to transport across a step. -/
lemma modalApplyOneS4Keyed_hasEdge_mono (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (modalApplyOneS4Keyed φ₀ keys sf b acc).snd.hasEdge w w' = true := by
  have hhasEdge_addEdge : ∀ (x y : WorldIndex), (acc.addEdge x y).hasEdge w w' = true := by
    intro x y
    simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
    simp [h]
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · rw [modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock,
            modalApplyOneS4KeyedMint_snd_eq]
        rcases modalApplyOne_fresh_local (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc with hsame | ⟨wsf, rest, -, hsnd⟩
        · rw [hsame]; exact h
        · rw [hsnd]; exact hhasEdge_addEdge _ _
      · rw [modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock]
        exact hhasEdge_addEdge _ _
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · rw [modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock,
            modalApplyOneS4KeyedMint_snd_eq]
        rcases modalApplyOne_fresh_local (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc with hsame | ⟨wsf, rest, -, hsnd⟩
        · rw [hsame]; exact h
        · rw [hsnd]; exact hhasEdge_addEdge _ _
      · rw [modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock]
        exact hhasEdge_addEdge _ _
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
      unfold modalApplyOneS4Keyed
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
        simp_all
    rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hnbd]
    -- Whether or not `sf` is boxPos/diaNeg-shaped, `modalApplyOneS4Rules`'s accessibility
    -- output is unconditionally K's own (`modalApplyOneS4Rules_snd_eq`), and K's own dichotomy
    -- (`modalApplyOne_fresh_local`) holds for `sf` regardless of its shape.
    rw [modalApplyOneS4Rules_snd_eq]
    rcases modalApplyOne_fresh_local sf b acc with hsame | ⟨wsf, rest, -, hsnd⟩
    · rw [hsame]; exact h
    · rw [hsnd]; exact hhasEdge_addEdge _ _

omit [Hashable Atom] in
/-- **Blocked-redirect witness membership**: when the keys-aware minting guard blocks
(redirects to `wBlock` instead of minting), the witness formula `⟨s, φ, wBlock⟩` the redirect
implicitly relies on is ALREADY on the branch `b` -- chained through `S4LoopInv.keyLowerBd`
(a world's recorded birth key lower-bounds its live relevant set) and the definitional
insert-membership of `successorBirthContent`. This is what lets `eBoxNegWitness`/
`eDiamondPosWitness` survive the blocked minting case below without asserting any new branch
formula (the blocked case's `.linear []` result adds none). -/
lemma modalStepBranchS4Keyed_blocked_witness_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ w = some wBlock) :
    (⟨s, φ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ w wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ w) hkey
  have hmem : (s, φ) ∈ successorBirthContent φ₀ b s φ w := by
    unfold successorBirthContent
    exact Finset.mem_insert_self _ _
  have hrel := hsub hmem
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

/-- **`modalApplyOneS4Keyed` is never expanding at the T/4-relevant shapes**
(`T(□φ)@w`, `F(◇φ)@w`): outside the two KEYED minting shapes (`F(□φ)@w`/`T(◇φ)@w` -- disjoint
from these), `modalApplyOneS4Keyed` falls through definitionally to `modalApplyOneS4`, which
itself falls through to `modalApplyOneS4Rules` at these same two shapes
(`modalApplyOneS4`'s own `| _, _ =>` catch-all). Composes
`modalApplyOneS4Rules_boxPos_diaNeg_known_S4` (same-file `private`) with that double
definitional fall-through. This is what makes `eBoxOnlyNeg`/`eDiamondOnlyPos` provable below: a
pos-box/neg-diamond formula can never be the `sf_exp` a `.linear`/`.branching` step appends to
`e`. -/
lemma modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneS4Keyed φ₀ keys sf b acc).fst = .notApplicable ∨
    ∃ out, (modalApplyOneS4Keyed φ₀ keys sf b acc).fst = .persistent out := by
  have heq : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4Rules sf b acc := by
    rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf
      subst hs; subst hf
      rfl
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf
      subst hs; subst hf
      rfl
  rw [heq]
  obtain ⟨-, hmatch⟩ := modalApplyOneS4Rules_boxPos_diaNeg_known_S4 sf b acc hsfmem hknown h
  rcases hres : (modalApplyOneS4Rules sf b acc).fst with nf | brs | nf | _
  · rw [hres] at hmatch; exact absurd hmatch (by simp)
  · rw [hres] at hmatch; exact absurd hmatch (by simp)
  · exact Or.inr ⟨nf, rfl⟩
  · exact Or.inl rfl

/-! ### 4-Rule Case Ingredients (Phase 7 of the S4 loop-guard soundness task)

The two 4-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`) never mint and never touch `acc`
(`modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding` above already established the
never-expanding half). The `.fst` closed forms and the Keyed→S4Rules bridge already exist above
(`modalApplyOneS4Rules_boxPos_fst`/`_diaNeg_fst`, `modalApplyOneS4Keyed_boxPos_eq_S4Rules`/
`_diaNeg_eq_S4Rules`, de-privatized for `FrameCompleteness.lean` to consume -- see their doc
comments above). Only the `.snd = acc` companion facts are new here (structural, no semantic
content); the actual K+T+4 `RuleResultSat` merge (semantic content, needs `FrameSoundness.lean`'s
`s4FC`/`sfSat` apparatus) lives in `FrameCompleteness.lean` per the layering note. -/

omit [Hashable Atom] in
/-- `modalApplyOneS4Rules`'s `.snd` at the box-positive shape is always `acc`, unconditionally:
chains the unconditional `modalApplyOneS4Rules_snd_eq` (same-file private, `.snd` always equals
K's own regardless of shape) with K's own box-positive `.snd` fact
(`modalApplyOne_boxPos_snd_S4`, same-file private). Not `private`: consumed by
`FrameCompleteness.lean`'s `modalApplyOneS4Rules_boxPos_soundIn`. -/
lemma modalApplyOneS4Rules_boxPos_snd_eq_acc
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4Rules (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc := by
  rw [modalApplyOneS4Rules_snd_eq, modalApplyOne_boxPos_snd_S4]

omit [Hashable Atom] in
/-- Dual of `modalApplyOneS4Rules_boxPos_snd_eq_acc` for the diamond-negative shape. -/
lemma modalApplyOneS4Rules_diaNeg_snd_eq_acc
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4Rules (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc := by
  rw [modalApplyOneS4Rules_snd_eq, modalApplyOne_diamondNeg_snd_S4]

/-- `modalApplyOneS4Keyed φ₀ keys sf b acc` at a non-box/diamond-shaped `sf` is exactly raw
K's `modalApplyOne sf b acc`, for ANY `keys` -- the dispatch chain `modalApplyOneS4Keyed →
modalApplyOneS4 → modalApplyOneS4Rules → modalApplyOneT → modalApplyOne` fires its catch-all arm
at every layer (mirrors the internal `hred` fact inside `modalApplyOneS4Keyed_fst_eq_of_not_box`,
extracted standalone since that lemma only exposes the branch/`acc`-invariance corollary, not the
underlying `keys`-independence).

Not `private`: consumed by `FrameCompleteness.lean`'s propositional-case ingredient for the
S4-keyed ordered driver's bespoke step-preservation lemma (Phase 7 of the S4 loop-guard
soundness task). -/
lemma modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneS4Keyed φ₀ keys (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOne (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc := by
  have heqS4 : modalApplyOneS4Keyed φ₀ keys
      (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneS4 φ₀ (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc := by
    unfold modalApplyOneS4Keyed
    rcases hs : s with _ | _ <;> rcases hf : φ with _ | _ | _ | _ | _ | ψ | ψ <;> simp_all
  rw [heqS4]
  have hnbd1 : ¬ ((⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).sign = .neg ∧
      ∃ ψ, (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).formula = .box ψ) ∧
      ¬ ((⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).sign = .pos ∧
      ∃ ψ, (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).formula = .diamond ψ) :=
    ⟨fun ⟨_, ψ, hfe⟩ => hnb ψ hfe, fun ⟨_, ψ, hfe⟩ => hnd ψ hfe⟩
  rw [modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc hnbd1]
  have hnbd2 : ¬ ((⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).sign = .pos ∧
      ∃ ψ, (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).formula = .box ψ) ∧
      ¬ ((⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).sign = .neg ∧
      ∃ ψ, (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex).formula = .diamond ψ) :=
    ⟨fun ⟨_, ψ, hfe⟩ => hnb ψ hfe, fun ⟨_, ψ, hfe⟩ => hnd ψ hfe⟩
  rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg _ b acc hnbd2,
      modalApplyOneT_eq_of_not_boxPos_diaNeg _ b acc hnbd2]

/-- Corollary of the above: `modalApplyOneS4Keyed φ₀ keys` and `modalApplyOneS4Keyed φ₀ keys'`
agree at any non-box/diamond-shaped signed formula, for ANY two `keys` lists -- both reduce to
the SAME `keys`-independent `modalApplyOne`. This is what lets `hintikkaInv`'s clauses for
box/diamond-EXCLUDED formulas (the only ones `modalHintikkaClauseGen` does not carve out as
vacuous `True`) transport from the OLD `keys` to the post-step `keys'` below. -/
private lemma modalApplyOneS4Keyed_keys_indep_of_not_box (φ₀ : Proposition Atom)
    (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneS4Keyed φ₀ keys (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneS4Keyed φ₀ keys' (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
          b acc := by
  rw [modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys s φ w hnb hnd b acc,
      modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box φ₀ keys' s φ w hnb hnd b acc]

/-- `modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys)` does not depend on `keys` at all:
vacuously `True` on both sides for box/diamond-shaped `φ` (by `modalHintikkaClauseGen`'s own
carve-out), and reduces to the SAME `keys`-independent `modalApplyOne` call for every other
shape (`modalApplyOneS4Keyed_keys_indep_of_not_box`). This is exactly what lets the single-
step preservation lift the OLD `e`'s `hintikkaInv` facts (stated over `keys`) to the post-step
`keys'` without re-deriving anything about the individual formulas of `e`. -/
lemma modalHintikkaClauseGen_S4Keyed_keys_indep (φ₀ : Proposition Atom)
    (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (X : List (SignedFormula (Proposition Atom) WorldIndex)) (Y : Accessibility) :
    modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys) s φ w X Y =
    modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys') s φ w X Y := by
  unfold modalHintikkaClauseGen
  rcases φ with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
  · rw [modalApplyOneS4Keyed_keys_indep_of_not_box φ₀ keys keys' s (.atom p) w
      (by simp) (by simp) X Y]
  · rw [modalApplyOneS4Keyed_keys_indep_of_not_box φ₀ keys keys' s .bot w
      (by simp) (by simp) X Y]
  · rw [modalApplyOneS4Keyed_keys_indep_of_not_box φ₀ keys keys' s (.imp a c) w
      (by simp) (by simp) X Y]
  · rw [modalApplyOneS4Keyed_keys_indep_of_not_box φ₀ keys keys' s (.and x y) w
      (by simp) (by simp) X Y]
  · rw [modalApplyOneS4Keyed_keys_indep_of_not_box φ₀ keys keys' s (.or x y) w
      (by simp) (by simp) X Y]
  · rfl
  · rfl

/-- The keyed box-negative rule is never `.notApplicable`: unblocked, it reduces to K's own
`modalApplyOne_boxNeg_witness` (always `.linear (_ :: _)`); blocked, it is `.linear []`
(`modalApplyOneS4Keyed_boxNeg_blocked_eq`). Either way the result constructor is `.linear`, never
`.notApplicable`. Guard-independent: holds for ANY `blockingWorldS4Keyed` outcome, so unaffected
by R1's guard-narrowing risk. -/
lemma modalApplyOneS4Keyed_boxNeg_ne_notApplicable (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4Keyed φ₀ keys
        (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).1
      ≠ .notApplicable := by
  rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ w with _ | wBlock
  · rw [modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ w hblock]
    obtain ⟨-, rest, hfst⟩ := modalApplyOneS4KeyedMint_boxNeg_witness b acc ψ w
    rw [hfst]; simp
  · rw [modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ w wBlock hblock]
    simp

/-- Dual of `modalApplyOneS4Keyed_boxNeg_ne_notApplicable` for the diamond-positive shape. -/
lemma modalApplyOneS4Keyed_diaPos_ne_notApplicable (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4Keyed φ₀ keys
        (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).1
      ≠ .notApplicable := by
  rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ w with _ | wBlock
  · rw [modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ w hblock]
    obtain ⟨-, rest, hfst⟩ := modalApplyOneS4KeyedMint_diaPos_witness b acc ψ w
    rw [hfst]; simp
  · rw [modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ w wBlock hblock]
    simp


end Cslib.Logic.Modal.Tableau

end
