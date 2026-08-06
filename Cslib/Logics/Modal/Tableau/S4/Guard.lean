/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.S4.Universe
public import Cslib.Logics.Modal.Tableau.S4.BirthKey

/-! # S4 Loop-Checking: Blocking Guard and Mint-Shape Predicates

The blocking-guard functions (`blockingWorldS4`, `blockingWorldS4Keyed`) that decide, for a
prospective fresh successor, whether an existing world already carries the same relevant
content and should be loop-backed to instead of minting; and `modalMintShape`, the decidable
predicate identifying the two signed-formula shapes (`F(□φ)@w`, `T(◇φ)@w`) at which the keyed
guard is consulted at all.

## Why a separate module

`blockingWorldS4{,Keyed}` are built directly from `BirthKey`'s `successorBirthContent` (the
loop-back comparison target) and `Universe`'s `relevantSetFinset`, and consumed by `Driver`
(above) at exactly the two `modalMintShape` shapes. This module sits between the two: it needs
nothing from `Driver`, and `Driver`'s minting arms need it before they can be stated. Keeping
it separate also isolates the guard's own unsoundness-history docstrings (`blockingWorldS4Keyed`
carries a substantial repair narrative) from both its dependencies and its consumer.

**Not here**: `modalNonMintCandidates` and its lemmas, despite sitting under the same
`## Mint-Readiness` doc-section heading as `modalMintShape` (and immediately after it in the
original file) -- `modalNonMintCandidates` is defined in terms of `modalApplyOneS4Keyed`, so it
belongs in `S4/Driver.lean` (Phase 5/6). The heading's prose is itself primarily about
`modalNonMintCandidates`'s settledness design and is left in place in `LoopChecking.lean`, where
it continues to introduce `modalNonMintCandidates` once this phase's declarations are removed
from between them.

## Main Definitions
- `blockingWorldS4`, `blockingWorldS4Keyed`: the blocking-guard functions.
- `modalMintShape`: the decidable minting-shape predicate.

## Main Results
- `blockingWorldS4_mem_modalKnownWorlds`, `_eq_birthContent`, `_none_fresh`: `blockingWorldS4`
  characterization.
- `blockingWorldS4Keyed_eq_birthContent`, `_none_fresh`: the keyed guard's analogues.
- `keysUpdate_preserves_keysDistinct`: keys-distinctness preservation under the keyed guard's
  block (references `blockingWorldS4Keyed`/`blockingWorldS4Keyed_none_fresh`, which is why this
  lives here rather than in `BirthKey` despite "keys" in its name -- research correction 1/4).
- `modalMintShape_boxNeg`, `_diaPos`, `_eq_false_of_not_boxNeg_diaPos`: the minting-shape
  characterization lemmas (the first two carry `@[simp]`, which travels with them unchanged).
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- The redesigned minting guard (fixes Gap 2): the least world `w' ∈ modalKnownWorlds b` whose
CURRENT relevant set (`relevantSetFinset`) already equals the PROSPECTIVE successor's birth
content (`successorBirthContent`), if any exists. `none` means no blocking world exists (the
underlying rule should mint a fresh world); `some wBlock` means the prospective successor
should be loop-backed to `wBlock` via a loop-back edge instead of minting a new world. Unlike
the old `blockingWorld`, no `w' ≠ w` side condition is needed: if `w` itself already carries
the prospective birth content, a reflexive loop-back edge `w → w` is a harmless, valid S4
degenerate case. -/
def blockingWorldS4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Option WorldIndex :=
  ((modalKnownWorlds b).filter
    (fun w' => decide (relevantSetFinset φ₀ b w' = successorBirthContent φ₀ b s φ w))).min?

omit [Hashable Atom] in
/-- If `blockingWorldS4` returns a world, it is a known world of the branch. -/
lemma blockingWorldS4_mem_modalKnownWorlds (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w wBlock : WorldIndex) (h : blockingWorldS4 φ₀ b s φ w = some wBlock) :
    wBlock ∈ modalKnownWorlds b := by
  have hmem := List.min?_mem h
  exact (List.mem_filter.mp hmem).1

omit [Hashable Atom] in
/-- **The guard contract** (replaces `blockingWorld_sameRelevantSet`): if `blockingWorldS4`
returns a world, that world's CURRENT relevant set equals the prospective successor's birth
content. This is exactly the fact the below `_preserves_keysDistinct` consumes: a freshly
minted world's key (its birth content) cannot coincide with any *other* existing world's key,
because if it did, the guard would have blocked and no new world would have been minted at
all. -/
lemma blockingWorldS4_eq_birthContent (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w wBlock : WorldIndex) (h : blockingWorldS4 φ₀ b s φ w = some wBlock) :
    relevantSetFinset φ₀ b wBlock = successorBirthContent φ₀ b s φ w := by
  have hmem := List.min?_mem h
  have hpred := (List.mem_filter.mp hmem).2
  exact of_decide_eq_true hpred

omit [Hashable Atom] in
/-- **The guard's freshness contract**: if `blockingWorldS4` returns `none`, the prospective
successor's birth content differs from every existing known world's CURRENT relevant set. This
is what makes a freshly-minted world's key distinct from every prior key (the `keysDistinct`
preservation obligation's minting case, below). -/
lemma blockingWorldS4_none_fresh (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w : WorldIndex) (h : blockingWorldS4 φ₀ b s φ w = none) :
    ∀ w' ∈ modalKnownWorlds b, relevantSetFinset φ₀ b w' ≠ successorBirthContent φ₀ b s φ w := by
  unfold blockingWorldS4 at h
  rw [List.min?_eq_none_iff, List.filter_eq_nil_iff] at h
  intro w' hw' heq
  exact absurd (decide_eq_true heq) (by simpa using h w' hw')

/-! ## Keys-Aware Minting Guard (closes the guard-vs-keys gap)

**The gap**: `blockingWorldS4` compares the prospective
successor's birth content against worlds' LIVE `relevantSetFinset`, but `S4LoopInv.keysDistinct`'s
preservation needs comparison against the RECORDED `keys` list directly. The chain
`k' ⊆ relevantSetFinset φ₀ b w'` (`keyLowerBd`) and `relevantSetFinset φ₀ b w' ≠ newkey`
(`blockingWorldS4_none_fresh`) does **not** imply `k' ≠ newkey`: if `k'` is a *proper* subset of
`w'`'s current relevant set (the expected case once ordinary saturation grows `w'`'s live set
past its birth key), `k' = newkey ⊊ relevantSetFinset φ₀ b w' ≠ newkey` is consistent, and
`keysDistinct` breaks the instant the new key is recorded.

`blockingWorldS4Keyed` below fixes this by comparing the prospective birth content directly
against `keys`, giving `keysDistinct`'s preservation for free from the guard's own freshness
contract -- no live-set indirection, no dependence on `keyLowerBd` being an equality.
`blockingWorldS4`/`modalApplyOneS4`/`modalHintikkaSetS4` remain
completely untouched as a separate, valid, live-set-guarded artifact that the
Hintikka/truth-lemma bridges continue to consume; `modalApplyOneS4Keyed`/`modalStepBranchS4Keyed`
below are the loop-invariant/termination track and consult ONLY the
keys-aware guard, bypassing `modalApplyOneS4`'s own internal (live-set) guard decision entirely
at the two minting shapes. -/

/-- The keys-aware minting guard: the least world `w'` **recorded** in `keys` whose recorded
birth key already equals the PROSPECTIVE successor's birth content, if any exists. Unlike
`blockingWorldS4` (live `relevantSetFinset`), this compares against the stable `keys` list.

**This guard, consumed unmodified by `modalStepBranchS4Keyed`, makes `modalTableauS4Keyed`
UNSOUND.** This is not an open conjecture: `CslibTests/S4LoopGuardRegression.lean` is a
machine-checked counterexample. Over two atoms `p0`, `p1` with `¬X := X → ⊥`, let
`αA := □p0 ∨ ¬¬◇p1`, `αL := □p0 ∨ ¬□p1`, `cex := □αA ∨ □αL`. `cex` has a 3-world
reflexive-transitive countermodel (`R = {(0,0),(0,1),(0,2),(1,1),(2,2)}`, `p1` true at world 1
only, `p0` false everywhere), so `cex` is not `s4Valid`; nonetheless the driver built on this
guard closes it.

The counterexample exercises two independent defects, and fixing one does **not** fix the
other:

- **Staleness.** This guard compares a prospective birth content against `keys` -- each world's
  content **as recorded at its minting**, not its current live content. In the trace, a world
  is minted with recorded key `{(neg, p0)}` before its later-minted sibling's own expansion has
  even started; that sibling's expansion subsequently adds formulas to the *first* world's live
  content, but its recorded key never moves. A second, unrelated world later computes the SAME
  prospective birth content `{(neg, p0)}` (evaluated before its own sibling formula has
  expanded, so it is also stale) and this guard reports a match against the first world's
  stale key. `blockingWorldS4` (the live-set guard) would instead compare against the live
  `relevantSetFinset`, which by then differs, and would correctly reject the block: this
  specific defect is unique to the keyed guard.
- **No reachability restriction.** The redirect edge this guard licenses connects the
  *source* world of the new minting attempt to the *blocking* world `w'`, with no constraint
  that `w'` be reachable from the source at all. In the trace this adds an edge between two
  worlds that are siblings under a common ancestor, not related to each other in any model.
  Soundness needs `m.r (f src) (f w')` in an arbitrary S4 frame, and nothing here supplies it.
  Persistent (box-positive) propagation then flows along this unjustified edge and manufactures
  a contradiction that no genuine countermodel has.

Fixing staleness alone (comparing against live content instead of recorded keys) does not fix
the reachability defect: the redirect edge is still unrestricted, so a live-set comparison that
happens to match is exposed to the same attack with different timing. The repair route under
development changes **when** a minting shape may fire (only once no non-minting rule can still
fire anywhere on the branch) rather than editing this comparison predicate -- an ordered
successor to the driver built on this guard, scheduled to land beside it as a parallel
definition before this one is retired. -/
def blockingWorldS4Keyed (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Option WorldIndex :=
  ((keys.filter
    (fun wk => decide (wk.2 = successorBirthContent φ₀ b s φ w))).map Prod.fst).min?

omit [Hashable Atom] in
/-- If `blockingWorldS4Keyed` returns a world, that world's RECORDED key equals the prospective
successor's birth content -- i.e. the pair is literally recorded in `keys`. -/
lemma blockingWorldS4Keyed_eq_birthContent (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w wBlock : WorldIndex)
    (h : blockingWorldS4Keyed φ₀ b keys s φ w = some wBlock) :
    (wBlock, successorBirthContent φ₀ b s φ w) ∈ keys := by
  unfold blockingWorldS4Keyed at h
  have hmem := List.min?_mem h
  simp only [List.mem_map] at hmem
  obtain ⟨wk, hwk_mem, hwk_fst⟩ := hmem
  have hwk_pred := (List.mem_filter.mp hwk_mem).2
  have heq : wk.2 = successorBirthContent φ₀ b s φ w := of_decide_eq_true hwk_pred
  have hwk_in : wk ∈ keys := (List.mem_filter.mp hwk_mem).1
  have hwk_eq : wk = (wBlock, successorBirthContent φ₀ b s φ w) := by
    rw [← hwk_fst, ← heq]
  rwa [hwk_eq] at hwk_in

omit [Hashable Atom] in
/-- **The keys-aware guard's freshness contract**: if `blockingWorldS4Keyed` returns `none`, the
prospective successor's birth content differs from every RECORDED key. This is exactly what
gives `keysDistinct`'s preservation directly (closing the gap
`blockingWorldS4_none_fresh` could not close on its own). -/
lemma blockingWorldS4Keyed_none_fresh (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (h : blockingWorldS4Keyed φ₀ b keys s φ w = none) :
    ∀ w' k', (w', k') ∈ keys → k' ≠ successorBirthContent φ₀ b s φ w := by
  unfold blockingWorldS4Keyed at h
  rw [List.min?_eq_none_iff] at h
  intro w' k' hmem heq
  have hfilt : (w', k') ∈ keys.filter
      (fun wk => decide (wk.2 = successorBirthContent φ₀ b s φ w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, decide_eq_true heq⟩
  have hmap : w' ∈ (keys.filter
      (fun wk => decide (wk.2 = successorBirthContent φ₀ b s φ w))).map Prod.fst :=
    List.mem_map_of_mem hfilt
  rw [h] at hmap
  simp at hmap

omit [Hashable Atom] in
/-- **The crux, closed**: the `keys`-update rule shared by both minting shapes
preserves `S4LoopInv.keysDistinct`. Unlike the old `blockingWorldS4`-driven update (the earlier
gap: `k' ⊆ relevantSetFinset φ₀ b w'` and `relevantSetFinset φ₀ b w' ≠ newkey` do NOT imply
`k' ≠ newkey` when `k'` is a proper subset), this needs no live-set indirection and no freshness
argument about the new world index at all: `blockingWorldS4Keyed_none_fresh` gives `k' ≠ newkey`
directly for every `(w', k') ∈ keys`, so the only remaining case (`w' = modalNextWorld b`, if it
were to occur) is excluded by `keysDistinct`'s own `w1 ≠ w2` hypothesis before `k1 ≠ k2` is ever
asked for. -/
lemma keysUpdate_preserves_keysDistinct (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hdistinct : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2) :
    ∀ w1 w2 k1 k2,
      (w1, k1) ∈ (match blockingWorldS4Keyed φ₀ b keys s φ w with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b s φ w)]) →
      (w2, k2) ∈ (match blockingWorldS4Keyed φ₀ b keys s φ w with
        | some _ => keys
        | none => keys ++ [(modalNextWorld b, successorBirthContent φ₀ b s φ w)]) →
      w1 ≠ w2 → k1 ≠ k2 := by
  cases hblock : blockingWorldS4Keyed φ₀ b keys s φ w with
  | some wBlock => exact hdistinct
  | none =>
    intro w1 w2 k1 k2 hmem1 hmem2 hne
    simp only [List.mem_append, List.mem_singleton] at hmem1 hmem2
    rcases hmem1 with hmem1 | hmem1 <;> rcases hmem2 with hmem2 | hmem2
    · exact hdistinct w1 w2 k1 k2 hmem1 hmem2 hne
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hmem2
      exact (blockingWorldS4Keyed_none_fresh φ₀ b keys s φ w hblock w1 k1 hmem1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hmem1
      exact fun heq =>
        (blockingWorldS4Keyed_none_fresh φ₀ b keys s φ w hblock w2 k2 hmem2) heq.symm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hmem1
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hmem2
      exact absurd rfl hne

/-! ## S4 Rule Application -/

/-- `true` exactly at the two minting shapes the keyed guard consults: `F(□φ)@w`
(box-negative) and `T(◇φ)@w` (diamond-positive) -- the two signed-formula shapes at which
`modalApplyOneS4Keyed` consults `blockingWorldS4Keyed` before falling through to the ordinary
rule set. -/
def modalMintShape (sf : SignedFormula (Proposition Atom) WorldIndex) : Bool :=
  match sf.sign, sf.formula with
  | .neg, .box _ => true
  | .pos, .diamond _ => true
  | _, _ => false

omit [DecidableEq Atom] [Hashable Atom] in
/-- `modalMintShape` characterisation, box-negative shape (`F(□φ)@w`). -/
@[simp]
lemma modalMintShape_boxNeg (φ : Proposition Atom) (w : WorldIndex) :
    modalMintShape (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) = true :=
  rfl

omit [DecidableEq Atom] [Hashable Atom] in
/-- `modalMintShape` characterisation, diamond-positive shape (`T(◇φ)@w`). -/
@[simp]
lemma modalMintShape_diaPos (φ : Proposition Atom) (w : WorldIndex) :
    modalMintShape (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) = true :=
  rfl

omit [DecidableEq Atom] [Hashable Atom] in
/-- `modalMintShape` is `false` at every signed-formula shape other than the two minting
shapes: the complement of the two characterisation lemmas above. -/
lemma modalMintShape_eq_false_of_not_boxNeg_diaPos
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (h : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalMintShape sf = false := by
  obtain ⟨h1, h2⟩ := h
  unfold modalMintShape
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all


end Cslib.Logic.Modal.Tableau

end
