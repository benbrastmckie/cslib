/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Dedup
public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.FrameRules

/-! # S4 Loop-Checking Machinery

This module builds the equality-blocking loop-checking machinery for the S4
(reflexive-transitive) modal tableau: per-world relevant-formula-set extraction, a
decidable equality test over `modalSubfmls φ₀`, the minting guard that consults this test
before creating a fresh world, the S4 rule-application function, and the S4 Hintikka-set
characterization.

S4 is deliberately **not** an instantiation of `RuleApplicationSpec` (`GenericDriver.lean`):
its transitively-propagating 4-rule places `T(□φ)` (unchanged modal depth) at successor
worlds, which falsifies the exact-decrement edge invariant (`rankStep`) that
`RuleApplicationSpec` demands. S4 reuses the generic driver (`modalStepBranchGen` etc.)
**definitionally only**, via a `φ₀`-parameterized `RuleApply` value, and supplies its own
sibling termination argument (`S4LoopInv`, a pigeonhole bound on `2 ^ (2 * |modalSubfmls φ₀|)`
possible signed-relevant-formula sets) instead of the K/T rank-decrease argument.

**Task 511 redesign**: the original `blockingWorld` guard and `worldSetsDistinct` invariant
(task 506) were both proved structurally unsound (task 511 research report) -- distinctness
over the *live* branch is not a loop invariant (relevant sets grow monotonically), and the
guard compared the *source* world's set rather than the *prospective successor's* birth
content. This module now uses `blockingWorldS4`/`successorBirthContent` (stable birth-content
guard) and `S4LoopInv`'s `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse` fields
(stable per-world birth keys) in their place.

## Main Definitions

- `formulasAtWorld`: the sub-list of a branch's signed formulas at a given world.
- `sameRelevantSet`: the decidable equality-of-relevant-formula-set test over
  `modalSubfmls φ₀`, used for comparison (retained as the comparison primitive, task 511).
- `signedSubfmls`/`relevantSetFinset`: the finite `Finset (Sign × Proposition Atom)` codomain
  and the live relevant set restated as a `Finset` (task 511 Phase 2).
- `successorBirthContent`/`blockingWorldS4`: the redesigned minting guard (task 511 Phase 3):
  blocks iff an existing known world's CURRENT relevant set equals the PROSPECTIVE successor's
  birth content, fixing Gap 2 (the old guard compared the source world's set instead).
- `modalApplyOneS4`: the `φ₀`-parameterized S4 rule-application function (Decision D1):
  at the two minting shapes, consult `blockingWorldS4` before falling through to the
  underlying rule's fresh-world minting.
- `modalStepBranchS4`/`modalExpandBranchesS4`/`modalTableauS4`: the S4 driver, reusing
  `Saturation.lean`'s generic driver **definitionally only** (no `RuleApplicationSpec`
  instance -- Correction 3).
- `modalHintikkaSetS4`: the S4 Hintikka-set characterization, a small delta over
  `modalHintikkaSet` (Decision D3).

## Strategy

Blocking is **equality-of-relevant-formula-set**, not subset-blocking: two worlds `w`,
`w'` are considered "the same" for loop-checking purposes exactly when they agree, for
every `ψ ∈ modalSubfmls φ₀` and every sign `s`, on whether `⟨s, ψ, w⟩` (`⟨s, ψ, w'⟩`
respectively) is on the branch. This is simpler than subset blocking and still yields a
`2 ^ (2 * |modalSubfmls φ₀|)` bound on the number of distinct worlds a saturating S4 tableau
can create (Phase 8), since each world's *birth key* is a distinct element of the powerset of
`modalSubfmls φ₀ × Sign` (task 511: the *birth key*, not the live relevant set, is what the
pigeonhole argument now injects -- see `S4LoopInv`).

Do **not** import `LoopInduction.lean`: despite the name, it is a `Forall2` list lemma
about the *fuel* loop in the generic driver, unrelated to modal loop-checking.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Per-World Formula Sets -/

/-- The sub-list of `b`'s signed formulas whose label is exactly `w`. -/
def formulasAtWorld (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) : List (SignedFormula (Proposition Atom) WorldIndex) :=
  b.filter (·.label == w)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Membership characterization for `formulasAtWorld`: a signed formula is in
`formulasAtWorld b w` iff it is in `b` and its label is `w`. -/
lemma mem_formulasAtWorld_iff (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) (sf : SignedFormula (Proposition Atom) WorldIndex) :
    sf ∈ formulasAtWorld b w ↔ sf ∈ b ∧ sf.label = w := by
  unfold formulasAtWorld
  simp [List.mem_filter, beq_iff_eq]

/-! ## Relevant-Formula-Set Equality Test -/

/-- The decidable equality-of-relevant-formula-set test that drives S4's loop-checking
minting guard: `true` exactly when `w` and `w'` agree, for every subformula `ψ` of `φ₀`
and every sign `s`, on whether `⟨s, ψ, w⟩` (resp. `⟨s, ψ, w'⟩`) is present on `b`.

This is stated directly over `b` (rather than via an intermediate sorted/deduped
relevant-formula list) precisely because a pointwise Boolean membership comparison, one
`ψ ∈ modalSubfmls φ₀` at a time, sidesteps any ordering concerns: `sameRelevantSet` is
manifestly reflexive and symmetric by construction (`Bool` equality is symmetric,
`Bool.beq_comm`-style), and transitive by chaining two equalities. -/
def sameRelevantSet (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w w' : WorldIndex) : Bool :=
  (modalSubfmls φ₀).all (fun ψ =>
    (b.any (· == (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
      == b.any (· == (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))) &&
    (b.any (· == (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
      == b.any (· == (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))))

/-- Bridge: `b.any (· == sf) = true ↔ sf ∈ b`, the standard membership bridge for the
`List.any (· == ·)` idiom used throughout the modal tableau development. -/
private lemma any_beq_iff_mem {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    l.any (· == a) = true ↔ a ∈ l := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxa⟩
    rw [beq_iff_eq] at hxa
    rwa [hxa] at hx
  · intro ha
    exact ⟨a, ha, by simp⟩

omit [Hashable Atom] in
/-- The characterization `sameRelevantSet` is built to serve: `sameRelevantSet φ₀ b w w'`
holds iff `w` and `w'` agree on membership of every relevant signed formula. This is what
Phase 8's pigeonhole argument consumes: `worldSetsDistinct` demands that every pair of
distinct known worlds *fails* this characterization. -/
lemma sameRelevantSet_iff (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w w' : WorldIndex) :
    sameRelevantSet φ₀ b w w' = true ↔
      ∀ (s : Sign) (ψ : Proposition Atom), ψ ∈ modalSubfmls φ₀ →
        ((⟨s, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ↔
         (⟨s, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) := by
  unfold sameRelevantSet
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h s ψ hψ
    obtain ⟨hpos, hneg⟩ := h ψ hψ
    rcases s with _ | _
    · rw [← any_beq_iff_mem, ← any_beq_iff_mem, hpos]
    · rw [← any_beq_iff_mem, ← any_beq_iff_mem, hneg]
  · intro h ψ hψ
    refine ⟨?_, ?_⟩
    · rw [Bool.eq_iff_iff, any_beq_iff_mem, any_beq_iff_mem]
      exact h .pos ψ hψ
    · rw [Bool.eq_iff_iff, any_beq_iff_mem, any_beq_iff_mem]
      exact h .neg ψ hψ

omit [Hashable Atom] in
/-- `sameRelevantSet` is reflexive: every world agrees with itself. -/
lemma sameRelevantSet_refl (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex) :
    sameRelevantSet φ₀ b w w = true := by
  rw [sameRelevantSet_iff]
  intro s ψ _
  rfl

omit [Hashable Atom] in
/-- `sameRelevantSet` is symmetric. -/
lemma sameRelevantSet_symm (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w w' : WorldIndex) :
    sameRelevantSet φ₀ b w w' = sameRelevantSet φ₀ b w' w := by
  by_cases h : sameRelevantSet φ₀ b w w' = true
  · have h' : sameRelevantSet φ₀ b w' w = true := by
      rw [sameRelevantSet_iff] at h ⊢
      intro s ψ hψ
      exact (h s ψ hψ).symm
    rw [h, h']
  · have hfalse : sameRelevantSet φ₀ b w w' = false := by
      rcases hb : sameRelevantSet φ₀ b w w' with _ | _
      · rfl
      · exact absurd hb h
    have hfalse' : sameRelevantSet φ₀ b w' w = false := by
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      apply h
      rw [sameRelevantSet_iff] at hcon ⊢
      intro s ψ hψ
      exact (hcon s ψ hψ).symm
    rw [hfalse, hfalse']

omit [Hashable Atom] in
/-- `sameRelevantSet` is transitive. -/
lemma sameRelevantSet_trans (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w w' w'' : WorldIndex)
    (h1 : sameRelevantSet φ₀ b w w' = true) (h2 : sameRelevantSet φ₀ b w' w'' = true) :
    sameRelevantSet φ₀ b w w'' = true := by
  rw [sameRelevantSet_iff] at h1 h2 ⊢
  intro s ψ hψ
  exact (h1 s ψ hψ).trans (h2 s ψ hψ)

/-! ## S4 World Bound (Decision D2)

`modalWorldBound`/`modalUniverse` (`FmpMeasure.lean`) are `(2*complexity+1)^(complexity+1)`,
a branching^depth *tree* bound: S4's world graph is not a bounded-depth tree (loop-back
edges make it a general DAG-with-cycles-collapsed), so this bound does not transfer.
`modalWorldBoundS4`/`modalUniverseS4` replace it with the pigeonhole bound
`2 ^ (2 * |modalSubfmls φ₀|)` -- the number of possible relevant-formula sets, i.e. the
cardinality of `powerset (Sign × modalSubfmls φ₀)` (task 511 research finding 3: the
`sameRelevantSet`/birth-key notion distinguishes *both signs*, so the pigeonhole codomain is
`powerset(Sign × Sf)`, not `powerset(Sf)`; `2^|Sf|` is unprovably small). `modalWork`/
`modalExpMeasure` (`FmpMeasure.lean`) are reused **verbatim**: they take the universe `U` as
an explicit parameter and are rule/world-agnostic. `geomCap`/`modalPotential`/
`modalPotentialTerm` do **not** transfer -- they are the geometric tree-capacity argument
specific to `modalWorldBound`. -/

/-- The S4 world bound: `2 ^ (2 * |modalSubfmls φ₀|)`, the number of possible
signed-relevant-formula sets, i.e. `(signedSubfmls φ₀).powerset.card` (Decision D2, corrected
per task 511 research finding 3). Replaces `modalWorldBound`'s branching^depth tree bound,
which does not apply to S4's (possibly cyclic) world graph. The `2·|Sf|` exponent (rather
than `|Sf|`) is required because the relevant-set/birth-key notion (`sameRelevantSet`,
`signedSubfmls`) distinguishes signs: the pigeonhole codomain is `powerset (Sign × Sf)`,
cardinality `2 ^ (2·|Sf|)`. Decidability only needs *a* computable finite bound, so this
looser value is harmless. -/
def modalWorldBoundS4 (φ₀ : Proposition Atom) : Nat :=
  2 ^ (2 * (modalSubfmls φ₀).length)

/-- The fixed finite signed-formula universe `U_{S4}(φ₀)`: both signs, every subformula of
`φ₀`, at every world label `0 .. modalWorldBoundS4 φ₀`. Mirrors `modalUniverse`
(`FmpMeasure.lean`) with `modalWorldBoundS4` swapped in for `modalWorldBound`. -/
def modalUniverseS4 (φ₀ : Proposition Atom) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (List.range (modalWorldBoundS4 φ₀ + 1)).flatMap (fun w =>
    (modalSubfmls φ₀).flatMap (fun ψ => [⟨.pos, ψ, w⟩, ⟨.neg, ψ, w⟩]))

/-- The S4 universe has length at most
`2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)`. Mirrors
`modalUniverse_length_le` (`FmpMeasure.lean`; that lemma carries the identical
`unusedDecidableInType` lint warning, unaddressed there too -- `DecidableEq Atom` is needed
by `SignedFormula`'s ambient instances even though the proof term itself never names it). -/
lemma modalUniverseS4_length_le (φ₀ : Proposition Atom) :
    (modalUniverseS4 φ₀).length ≤
      2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by
  have hinner : ∀ w : WorldIndex,
      ((modalSubfmls φ₀).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                    ⟨.neg, ψ, w⟩])).length
        ≤ 2 * (2 * modalComplexity φ₀ + 1) := by
    intro w
    rw [List.length_flatMap]
    have hb : (List.map (fun ψ =>
        ([(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex), ⟨.neg, ψ, w⟩]).length)
        (modalSubfmls φ₀)).sum ≤ (modalSubfmls φ₀).length * 2 :=
      sum_map_le_length_mul (modalSubfmls φ₀) _ 2 (fun ψ _ => by simp)
    have hlen := modalSubfmls_length_le φ₀
    omega
  unfold modalUniverseS4
  rw [List.length_flatMap]
  have houter : (List.map (fun w =>
      ((modalSubfmls φ₀).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                    ⟨.neg, ψ, w⟩])).length) (List.range (modalWorldBoundS4 φ₀ + 1))).sum
      ≤ (List.range (modalWorldBoundS4 φ₀ + 1)).length * (2 * (2 * modalComplexity φ₀ + 1)) :=
    sum_map_le_length_mul (List.range (modalWorldBoundS4 φ₀ + 1)) _
      (2 * (2 * modalComplexity φ₀ + 1)) (fun w _ => hinner w)
  rw [List.length_range] at houter
  calc (List.map (fun w =>
        ((modalSubfmls φ₀).flatMap
          (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                      ⟨.neg, ψ, w⟩])).length) (List.range (modalWorldBoundS4 φ₀ + 1))).sum
      ≤ (modalWorldBoundS4 φ₀ + 1) * (2 * (2 * modalComplexity φ₀ + 1)) := houter
    _ = 2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by ring

/-! ## Signed-Key Finite Codomain (task 511, Phase 2)

The stable-key infrastructure the redesigned guard/invariant (Phases 3-6) consumes: the fixed
finite codomain `signedSubfmls φ₀` (both signs × every subformula of `φ₀`, as a `Finset`) and
the live relevant set `relevantSetFinset φ₀ b w` restated as a `Finset` (reusing
`sameRelevantSet`'s membership notion). No driver change here -- pure defs + lemmas,
CI-green in isolation. -/

/-- The finite signed-subformula codomain: both signs paired with every subformula of `φ₀`, as
a `Finset (Sign × Proposition Atom)`. This is the fixed codomain the pigeonhole argument
(`modalKnownWorlds_length_le_worldBoundS4`, Phase 6) injects known worlds into, via their birth
keys (`S4LoopInv.keysInUniverse`). -/
def signedSubfmls (φ₀ : Proposition Atom) : Finset (Sign × Proposition Atom) :=
  ({Sign.pos, Sign.neg} : Finset Sign) ×ˢ (modalSubfmls φ₀).toFinset

omit [Hashable Atom] in
/-- `signedSubfmls φ₀`'s cardinality is at most `2 * |modalSubfmls φ₀|` (equality would need
`modalSubfmls φ₀` duplicate-free; the pigeonhole argument only needs the inequality, since it
feeds `Nat.pow_le_pow_right` toward `modalWorldBoundS4 φ₀ = 2 ^ (2 * |modalSubfmls φ₀|)`, an
upper bound is all that is required). -/
lemma signedSubfmls_card_le (φ₀ : Proposition Atom) :
    (signedSubfmls φ₀).card ≤ 2 * (modalSubfmls φ₀).length := by
  unfold signedSubfmls
  rw [Finset.card_product]
  have h2 : ({Sign.pos, Sign.neg} : Finset Sign).card = 2 := by decide
  rw [h2]
  have hle := List.toFinset_card_le (modalSubfmls φ₀)
  omega

omit [Hashable Atom] in
/-- The powerset of `signedSubfmls φ₀` has cardinality at most `modalWorldBoundS4 φ₀`: the
cardinality bridge Phase 6's pigeonhole argument consumes (`Finset.card_powerset` plus
`signedSubfmls_card_le`, monotone in the exponent). This is why Phase 1 (the exponent fix)
precedes: it ties the bound to `2 ^ (2·|Sf|)`, the correct codomain size for a sign-distinguishing
key. -/
lemma signedSubfmls_powerset_card_le (φ₀ : Proposition Atom) :
    (signedSubfmls φ₀).powerset.card ≤ modalWorldBoundS4 φ₀ := by
  unfold modalWorldBoundS4
  rw [Finset.card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) (signedSubfmls_card_le φ₀)

/-- The live relevant set `R(b,w)` (task 511 research §1.3) as a `Finset`: exactly the
elements of `signedSubfmls φ₀` whose signed-formula instantiation at `w` is present on `b`.
Reuses `sameRelevantSet`'s membership notion (`⟨s,ψ,w⟩ ∈ b`) restated as a finite set for the
birth-key / pigeonhole machinery (Phases 3-6). -/
def relevantSetFinset (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex) :
    Finset (Sign × Proposition Atom) :=
  (signedSubfmls φ₀).filter
    (fun p => b.any (· == (⟨p.1, p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex)))

omit [Hashable Atom] in
/-- `relevantSetFinset φ₀ b w` is (trivially, by construction as a filter of `signedSubfmls
φ₀`) a subset of `signedSubfmls φ₀`. This is `S4LoopInv.keysInUniverse`'s per-world content
once composed with `S4LoopInv.keyLowerBd`. -/
lemma relevantSetFinset_subset_signedSubfmls (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex) :
    relevantSetFinset φ₀ b w ⊆ signedSubfmls φ₀ :=
  Finset.filter_subset _ _

omit [Hashable Atom] in
/-- `relevantSetFinset` is monotone in the branch: if every formula of `b` is also a formula
of `b'`, then `w`'s relevant set over `b` is a subset of `w`'s relevant set over `b'`. This is
the fact Gap 1 (task 511 research §2) exploited for the old live-branch invariant, and the
fact the new lower-bound invariant (`S4LoopInv.keyLowerBd`, Phase 4) is designed to *survive*:
birth keys are fixed, but the live relevant set they lower-bound only grows. -/
lemma relevantSetFinset_mono (φ₀ : Proposition Atom)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hsub : ∀ sf ∈ b, sf ∈ b') :
    relevantSetFinset φ₀ b w ⊆ relevantSetFinset φ₀ b' w := by
  unfold relevantSetFinset
  apply Finset.monotone_filter_right
  intro p _ hp
  simp only [List.any_eq_true, beq_iff_eq] at hp ⊢
  obtain ⟨sf, hsf_mem, heq⟩ := hp
  exact ⟨sf, hsub sf hsf_mem, heq⟩

/-! ## Minting Guard (task 511, Phase 3: redesigned to fix Gap 2)

**Gap 2** (task 511 research §2): the *original* `blockingWorld` guard compared the *source*
world `w`'s own relevant set against other known worlds' sets -- but the newly-minted world
`w'`'s actual birth content (`successorBirthContent` below) is unrelated to `R(b,w)` (it is
the witness formula plus the *unwrapped* box-context transmitted from `w`, not `w`'s own
relevant-formula membership). So the old guard's check was neither necessary nor sufficient
for the property it was meant to enforce. The redesigned guard `blockingWorldS4` compares
against the **prospective successor's own birth content** instead, closing the gap. -/

/-- The prospective birth content of the successor that would be minted for the modal-minting
call at `⟨s, φ, w⟩` (the two K minting shapes `F(□φ)@w`/`T(◇φ)@w`, `s` the witness's sign) at
branch `b`: the witness signed pair `(s, φ)` together with the S4 box-context transmitted from
`w` -- `(Sign.pos, ψ)` for every `T(□ψ)@w ∈ b` and `(Sign.neg, ψ)` for every `F(◇ψ)@w ∈ b`.
Matches the actual K-minting birth content (`modalApplyOne`'s `boxNeg`/`diamondPos` arms,
`Rules.lean`), restricted to `signedSubfmls φ₀`-relevant pairs. Computed entirely from data
already on `b` at mint time; stable (never recomputed once the world is born) -- this is
exactly the property that makes `S4LoopInv.keyLowerBd` (Phase 4) a genuine loop invariant
where the old `worldSetsDistinct` (over the live branch) was not (Gap 1). -/
def successorBirthContent (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Finset (Sign × Proposition Atom) :=
  insert (s, φ) ((signedSubfmls φ₀).filter (fun p =>
    (p.1 = Sign.pos ∧
      b.any (· == (⟨.pos, .box p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex))) ∨
    (p.1 = Sign.neg ∧
      b.any (· == (⟨.neg, .diamond p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex)))))

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
content. This is exactly the fact Phase 5's `_preserves_keysDistinct` consumes: a freshly
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
preservation obligation's minting case, Phase 5). -/
lemma blockingWorldS4_none_fresh (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (s : Sign) (φ : Proposition Atom)
    (w : WorldIndex) (h : blockingWorldS4 φ₀ b s φ w = none) :
    ∀ w' ∈ modalKnownWorlds b, relevantSetFinset φ₀ b w' ≠ successorBirthContent φ₀ b s φ w := by
  unfold blockingWorldS4 at h
  rw [List.min?_eq_none_iff, List.filter_eq_nil_iff] at h
  intro w' hw' heq
  exact absurd (decide_eq_true heq) (by simpa using h w' hw')

/-! ## Keys-Aware Minting Guard (task 511, Phase 5: closes the guard-vs-keys gap)

**The Phase 5 blocker** (this plan, Phase 5 section): `blockingWorldS4` compares the prospective
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
`blockingWorldS4`/`modalApplyOneS4`/`modalHintikkaSetS4` (task 511 Phase 3, task 506) remain
completely untouched as a separate, valid, live-set-guarded artifact that task 506's
Hintikka/truth-lemma bridges continue to consume; `modalApplyOneS4Keyed`/`modalStepBranchS4Keyed`
below are the loop-invariant/termination track (this plan's Phases 5-7) and consult ONLY the
keys-aware guard, bypassing `modalApplyOneS4`'s own internal (live-set) guard decision entirely
at the two minting shapes (blocker's Option (a)). -/

/-- The keys-aware minting guard: the least world `w'` **recorded** in `keys` whose recorded
birth key already equals the PROSPECTIVE successor's birth content, if any exists. Unlike
`blockingWorldS4` (live `relevantSetFinset`), this compares against the stable `keys` list. -/
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
gives `keysDistinct`'s preservation directly (Phase 5's crux, closing the gap
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
/-- **Phase 5's named crux, closed**: the `keys`-update rule shared by both minting shapes
preserves `S4LoopInv.keysDistinct`. Unlike the old `blockingWorldS4`-driven update (Phase 5's
blocker: `k' ⊆ relevantSetFinset φ₀ b w'` and `relevantSetFinset φ₀ b w' ≠ newkey` do NOT imply
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

/-- The `φ₀`-parameterized S4 rule-application function (Decision D1). Wraps
`modalApplyOneS4Rules` (K + T + 4, `FrameRules.lean`). At the two **minting** shapes
(`F(□φ)@w`, `T(◇φ)@w` -- the shapes where the underlying K rule would create a fresh
world), consults `blockingWorldS4` (task 511 Phase 3: fixes Gap 2, the guard now compares the
*prospective successor's* birth content, not the source world `w`'s own set):
- **blocked** (`some wBlock`): returns `.linear []` and `acc.addEdge w wBlock` -- a
  loop-back edge to the existing blocking world, minting **no** new world.
- **unblocked** (`none`): falls through unchanged to `modalApplyOneS4Rules` (hence to the
  underlying rule's fresh-world minting, `modalApplyOneS4_unblocked_eq` below).

This is the one place S4 departs structurally from K: everywhere else, `modalApplyOneS4`
is exactly `modalApplyOneS4Rules`.

**Design note (deviation from a literal reading of the plan)**: the blocked case uses
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
(`modalApplyOne`), which mints exactly `modalNextWorld b`. This is Phase 8's dispatch entry
point for the box-negative minting shape. -/
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

/-! ## Key-Threaded S4 Step (task 511, Phase 4)

`worldSetsDistinct`, stated over the *live* branch, is not a loop invariant (Gap 1, task 511
research §2): a persistent step can fill in the one coordinate on which two worlds' relevant
sets differed, collapsing them. The fix (Option A2) threads a **stable per-world birth key**
list alongside `(b, e, acc)`: keys are fixed at minting time and never touched again, so a
lower-bound-style invariant stated over them survives every subsequent step. This is *the*
place S4 stops reusing `modalStepBranchGen` definitionally for **stepping** (it still reuses
`modalApplyOneS4 φ₀` -- the K/T/4 rule slot -- for all formula-level work); Phase 9's own loop
needs an S4-specific driver regardless (task 511 research §3), so this cost is not incurred
twice. -/

/-- **Task 511 Phase 5 revision**: the keys-aware S4 rule-application function, closing the
guard-vs-keys gap. Identical in shape to `modalApplyOneS4 φ₀` (same non-minting fallthrough to
`modalApplyOneS4Rules`/`modalApplyOneS4`), but at the two minting shapes consults
`blockingWorldS4Keyed φ₀ b keys` (the RECORDED-keys guard) instead of `blockingWorldS4` (the
live-set guard). This is what makes `modalStepBranchS4Keyed`'s `(b, e, acc)` bookkeeping and its
`keys` bookkeeping driven by the SAME decision -- required for `S4LoopInv.keyLowerBd` to remain
consistent with `S4LoopInv.keysDistinct` (blocker Option (a)): if the two bookkeeping streams
used different guards, a world could be recorded in `keys` without ever actually being minted
onto the branch, breaking `keyLowerBd` (`k ⊆ relevantSetFinset φ₀ b w` fails when `w` was never
minted, since then `relevantSetFinset φ₀ b w = ∅ ⊉ k` for nonempty `k`). Reduces to
`modalApplyOne` (raw K) at an unblocked minting shape -- same underlying rule as
`modalApplyOneS4`'s own unblocked reduction (`modalApplyOneS4_boxNeg_unblocked_eq`/dual), just
gated by a different guard. `modalApplyOneS4`/`blockingWorldS4` are NOT modified or removed:
they remain the live-set-guarded artifact task 506's Hintikka/truth-lemma bridges consume. -/
def modalApplyOneS4Keyed (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : RuleApply Atom :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box φ =>
      match blockingWorldS4Keyed φ₀ b keys .neg φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOne sf b acc
    | .pos, .diamond φ =>
      match blockingWorldS4Keyed φ₀ b keys .pos φ sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOne sf b acc
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

/-- Guard spec, box-negative shape, unblocked case: reduces to the raw K rule
(`modalApplyOne`). -/
lemma modalApplyOneS4Keyed_boxNeg_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (φ : Proposition Atom) (w : WorldIndex)
    (hblock : blockingWorldS4Keyed φ₀ b keys .neg φ w = none) :
    modalApplyOneS4Keyed φ₀ keys ⟨.neg, .box φ, w⟩ b acc
      = modalApplyOne ⟨.neg, .box φ, w⟩ b acc := by
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

/-- Guard spec, diamond-positive shape, unblocked case: reduces to the raw K rule. -/
lemma modalApplyOneS4Keyed_diaPos_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (φ : Proposition Atom) (w : WorldIndex)
    (hblock : blockingWorldS4Keyed φ₀ b keys .pos φ w = none) :
    modalApplyOneS4Keyed φ₀ keys ⟨.pos, .diamond φ, w⟩ b acc
      = modalApplyOne ⟨.pos, .diamond φ, w⟩ b acc := by
  unfold modalApplyOneS4Keyed
  simp [hblock]

/-- The S4-specific keyed one-step branch expansion: same selected formula (`b.findSome?` over
the same "already expanded" guard) and same rule application (`modalApplyOneS4Keyed φ₀ keys`,
task 511 Phase 5) as the `(newBranches, newExpandedSets, newAcc)` triple -- additionally threads
a `keys` list recording every known world's stable birth content. On a call at one of the two
minting shapes that is **not** blocked (`blockingWorldS4Keyed φ₀ b keys s φ w = none`), the
underlying rule mints `modalNextWorld b`, so `keys` gains the entry `(modalNextWorld b,
successorBirthContent φ₀ b s φ w)`. On every other call (blocked minting-shaped, or a
non-minting shape entirely), no world is minted and `keys` is unchanged. The keys' computation
below re-derives the SAME `blockingWorldS4Keyed` decision `modalApplyOneS4Keyed` already made
internally (rather than threading it out), keeping this definition's shape close to Phase 4's
original for auditability. -/
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

/-! ## Minting-Content Groundwork (task 511, Phase 5): towards `successorBirthContent`
matching the actual K-minting payload

`successorBirthContent` was *designed* to match `modalApplyOne`'s box-neg/diamond-pos minting
payload (its own docstring): `keyLowerBd`'s minting case needs the fresh world's
`relevantSetFinset` (over the POST-step branch) to equal the prospective birth content computed
PRE-step. This section lands the REUSABLE groundwork for that equality (subformula-membership
extraction so the witness lands in `signedSubfmls φ₀`, plus the literal `.fst` unfolding of
`modalApplyOne` at both minting shapes) but the equality lemma itself did **not** close within
this dispatch's budget -- see this plan's Phase 5 section for the current, narrowed blocker
(the guard-vs-keys gap itself IS closed; this remaining piece is pure Lean/`Bool`-vs-`Prop`
proof engineering, not a further structural gap). -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Transitivity of `modalSubfmls`: a subformula of a subformula is a subformula.
`FmpMeasure.lean`'s `modalSubfmls_trans` is file-private (as are its siblings `_B`/`_S5`/`_Five`
in their own files); this is the S4-local copy, needed to derive `φ ∈ modalSubfmls φ₀` (hence
`signedSubfmls` membership) for the box/diamond witness in the minting-content equality this
groundwork supports. -/
private lemma modalSubfmls_trans_S4 {a b c : Proposition Atom}
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
/-- Extraction: the formula-component of any `modalUniverseS4 φ₀` member is a subformula of
`φ₀`. S4-local restatement of `FmpMeasure.lean`'s file-private `modalUniverse_mem_formula`. -/
private lemma modalUniverseS4_mem_formula {φ₀ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverseS4 φ₀) :
    x.formula ∈ modalSubfmls φ₀ := by
  simp only [modalUniverseS4, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, -, ψ, hψ, heq | heq⟩ := hx <;> (subst heq; exact hψ)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Extraction: the label-component of any `modalUniverseS4 φ₀` member is bounded by
`modalWorldBoundS4 φ₀`. S4-local restatement of `FmpMeasure.lean`'s file-private
`modalUniverse_mem_label` (task 511, Phase 6 groundwork). -/
private lemma modalUniverseS4_mem_label {φ₀ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverseS4 φ₀) :
    x.label ≤ modalWorldBoundS4 φ₀ := by
  simp only [modalUniverseS4, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, ψ, -, heq | heq⟩ := hx <;> (subst heq; exact Nat.lt_succ_iff.mp hw)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Constructor direction for `modalUniverseS4` membership: a signed formula with any sign,
a subformula of `φ₀`, at a world label within the bound, is in `U_{S4}(φ₀)`. S4-local
restatement of `FmpMeasure.lean`'s file-private `mem_modalUniverse_of` (task 511, Phase 6
groundwork). -/
private lemma mem_modalUniverseS4_of {φ₀ : Proposition Atom} {s : Sign} {φ : Proposition Atom}
    {w : WorldIndex} (hw : w ≤ modalWorldBoundS4 φ₀) (hφ : φ ∈ modalSubfmls φ₀) :
    (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverseS4 φ₀ := by
  have hlt : w < modalWorldBoundS4 φ₀ + 1 := Nat.lt_succ_of_le hw
  simp only [modalUniverseS4, List.mem_flatMap, List.mem_range]
  exact ⟨w, hlt, φ, hφ, by cases s <;> simp⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Generic form of `mem_modalUniverseS4_of`, stated for an arbitrary signed formula `z` rather
than a literal anonymous constructor (needed by case-split proofs over already-opaque signed
formulas). S4-local restatement of `FmpMeasure.lean`'s file-private `mem_modalUniverse_of'`. -/
private lemma mem_modalUniverseS4_of' {φ₀ : Proposition Atom}
    {z : SignedFormula (Proposition Atom) WorldIndex}
    (hw : z.label ≤ modalWorldBoundS4 φ₀) (hφ : z.formula ∈ modalSubfmls φ₀) :
    z ∈ modalUniverseS4 φ₀ := by
  obtain ⟨s, φ, w⟩ := z
  exact mem_modalUniverseS4_of hw hφ

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

/-! ## Minting-Content Universe-Membership (task 511, Phase 6 groundwork for `bClosure`)

S4-local restatements of `FmpMeasure.lean`'s file-private Phase 1a/1b closure facts
(`mem_boxPositivesOf`/`boxProps_outputs_subset`/`diaNegProps_outputs_subset`/
`modalApplyOne_diamondPos_outputs_subset`/`modalApplyOne_boxNeg_outputs_subset`), retargeted
from `modalUniverse`/`modalWorldBound` to `modalUniverseS4`/`modalWorldBoundS4`. These give the
`modalUniverseS4 φ₀` membership bound for `modalApplyOne`'s two minting shapes' literal output
content (`modalApplyOne_boxNeg_mint_fst_S4`/`modalApplyOne_diamondPos_mint_fst_S4`'s payload),
consumed by `modalStepBranchS4_preserves_bClosure`'s two minting-shape cases. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion for `boxPositivesOf`: every `(ψ, src)` pair it returns came from an actual
`T(□ψ)@src` member of the branch. S4-local restatement of `FmpMeasure.lean`'s file-private
`mem_boxPositivesOf`. -/
private lemma mem_boxPositivesOf_S4 {b : List (SignedFormula (Proposition Atom) WorldIndex)}
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
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := mem_boxPositivesOf_S4 hψsrc
      have hψsub : (Proposition.box ψ) ∈ modalSubfmls φ₀ :=
        modalUniverseS4_mem_formula (hb _ hψbox)
      have hψmem : ψ ∈ modalSubfmls (Proposition.box ψ) := by simp [modalSubfmls]
      exact mem_modalUniverseS4_of hwbound (modalSubfmls_trans_S4 hψmem hψsub)
  · simp at heq

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
        exact mem_modalUniverseS4_of hwbound (modalSubfmls_trans_S4 hψmem hψsub)
    · simp at heq
  · simp at heq

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
    x ∈ modalUniverseS4 φ₀ := by
  have hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀ := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ₀ :=
    modalUniverseS4_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) := by simp [modalSubfmls]
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hbox) | hdia
  · exact mem_modalUniverseS4_of hwbound (modalSubfmls_trans_S4 hφmem hsrc)
  · exact boxProps_outputs_subset_S4 φ₀ b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset_S4 φ₀ b w hb hwbound x hdia

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
    x ∈ modalUniverseS4 φ₀ := by
  have hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀ := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.box φ) ∈ modalSubfmls φ₀ := modalUniverseS4_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls (Proposition.box φ) := by simp [modalSubfmls]
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hbox) | hdia
  · exact mem_modalUniverseS4_of hwbound (modalSubfmls_trans_S4 hφmem hsrc)
  · exact boxProps_outputs_subset_S4 φ₀ b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset_S4 φ₀ b w hb hwbound x hdia

/-! ## Minting-Content Equality Closure (task 511, Phase 5 continuation)

This section closes the gap the prior dispatch narrowed but did not finish: `keyLowerBd`'s
minting case, `successorBirthContent φ₀ b s φ w ⊆ relevantSetFinset φ₀ (newForms ++ b)
(modalNextWorld b)`. `keyLowerBd` itself only demands `⊆` (not `=`), so only the forward
direction is proved -- narrower than the prior dispatch's `Finset.ext` attempt, which chased
the (unneeded for this obligation) reverse direction too and got stuck bridging `Bool`-valued
`List.any` against the target `Prop`. The technique here avoids that bridge entirely: convert
every `List.any (· == t) = true`/`= false` fact to/from a plain `t ∈ l`/`t ∉ l` membership fact
immediately (`any_beq_of_mem_S4`/`mem_of_any_beq_S4`), then work purely with `List.mem_*`
combinators and `List.mem_filterMap`. -/

omit [Hashable Atom] in
/-- If `t ∈ l`, then `l.any (· == t) = true`. Converts a `List.mem` fact into the `Bool`-valued
form `relevantSetFinset`/`successorBirthContent` filter on. -/
private lemma any_beq_of_mem_S4 {l : List (SignedFormula (Proposition Atom) WorldIndex)}
    {t : SignedFormula (Proposition Atom) WorldIndex} (h : t ∈ l) : l.any (· == t) = true := by
  rw [List.any_eq_true]
  exact ⟨t, h, by simp⟩

omit [Hashable Atom] in
/-- Converse of `any_beq_of_mem_S4`: `l.any (· == t) = true` gives `t ∈ l`. -/
private lemma mem_of_any_beq_S4 {l : List (SignedFormula (Proposition Atom) WorldIndex)}
    {t : SignedFormula (Proposition Atom) WorldIndex} (h : l.any (· == t) = true) : t ∈ l := by
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxeq⟩ := h
  rw [beq_iff_eq] at hxeq
  rwa [hxeq] at hx

omit [Hashable Atom] in
/-- Freshness, in `any`-form: if `t`'s label is the fresh world `modalNextWorld b`, `t` cannot
be found on `b` (`modalNextWorld_gt`'s contrapositive). This is what makes every dedup guard
inside `modalApplyOne`'s minting arms take the "not yet present" branch when consumed against
the freshly-minted label. -/
private lemma modalNextWorld_fresh_beq_S4
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (t : SignedFormula (Proposition Atom) WorldIndex) (ht : t.label = modalNextWorld b) :
    b.any (· == t) = false := by
  by_contra hcontra
  rw [Bool.not_eq_false] at hcontra
  have hmem := mem_of_any_beq_S4 hcontra
  have hlt := modalNextWorld_gt b t hmem
  exact absurd (ht ▸ hlt) (lt_irrefl _)

omit [Hashable Atom] in
/-- Any `Sign` value is a member of `signedSubfmls φ₀`'s sign component (`{pos, neg}` is the
whole type), so `signedSubfmls` membership reduces to the formula component alone
(S4-local restatement of `S5Simplification.lean`'s file-private `mem_signedSubfmls_of_formula_S5w`,
needed here since `signedSubfmls` is defined in this file but that lemma is file-private there). -/
private lemma mem_signedSubfmls_of_formula_S4 {φ₀ : Proposition Atom} (s : Sign)
    {ψ : Proposition Atom} (h : ψ ∈ modalSubfmls φ₀) : (s, ψ) ∈ signedSubfmls φ₀ := by
  simp only [signedSubfmls, Finset.mem_product, List.mem_toFinset]
  refine ⟨?_, h⟩
  cases s <;> simp

/-- **`keyLowerBd`'s minting case, box-negative shape**: the prospective birth content computed
PRE-step (`successorBirthContent`) is a subset of the freshly-minted world's relevant set
computed POST-step (`relevantSetFinset` over `newForms ++ b`). Consumes `modalApplyOne`'s
literal box-neg minting payload (`modalApplyOne_boxNeg_mint_fst_S4`) via the `hnewForms`
hypothesis (stated in terms of `modalApplyOne` rather than the raw payload literal, so the
caller only needs `modalApplyOne`'s actual output, not to hand-reconstruct its list shape) plus
the branch-closure witness fact (`hb`/`hsf`, via `modalUniverseS4_mem_formula`/
`modalSubfmls_trans_S4`) that the witness formula `φ` itself lies in `signedSubfmls φ₀`. -/
private lemma successorBirthContent_boxNeg_subset_relevantSetFinset
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (φ : Proposition Atom)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsf : (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (newForms : List (SignedFormula (Proposition Atom) WorldIndex))
    (hnewForms : (modalApplyOne (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst = RuleResult.linear newForms) :
    successorBirthContent φ₀ b .neg φ w ⊆
      relevantSetFinset φ₀ (newForms ++ b) (modalNextWorld b) := by
  rw [modalApplyOne_boxNeg_mint_fst_S4] at hnewForms
  injection hnewForms with hnewForms
  subst hnewForms
  have hφsub : φ ∈ modalSubfmls φ₀ := by
    have h1 : (Proposition.box φ) ∈ modalSubfmls φ₀ := modalUniverseS4_mem_formula (hb _ hsf)
    have h2 : φ ∈ modalSubfmls (Proposition.box φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
    exact modalSubfmls_trans_S4 h2 h1
  have hwit : ((Sign.neg, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀ :=
    mem_signedSubfmls_of_formula_S4 .neg hφsub
  intro p hp
  simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨hpmem, hdisj⟩
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hwit, any_beq_of_mem_S4 ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hpmem, any_beq_of_mem_S4 ?_⟩
    rcases hdisj with ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩
    · -- box-positive transmission: p.1 = pos, T(□p.2)@w ∈ b
      have hbmem : (⟨.pos, .box p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hbp : (p.2, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box p.2, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          (boxPositivesOf b).filterMap (fun (ψ, src) =>
            if src == w then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
              if b.any (· == sf') then none else some sf'
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨(p.2, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ htarget))
    · -- diamond-negative transmission: p.1 = neg, F(◇p.2)@w ∈ b
      have hbmem : (⟨.neg, .diamond p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hdedup : b.any (· == (⟨.neg, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          b.filterMap (fun sf' =>
            if sf'.sign == .neg && sf'.label == w then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex :=
                  ⟨.neg, ψ, modalNextWorld b⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨⟨.neg, .diamond p.2, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)

/-- **`keyLowerBd`'s minting case, diamond-positive shape** (dual of the box-negative case):
the prospective birth content computed PRE-step is a subset of the freshly-minted world's
relevant set computed POST-step. -/
private lemma successorBirthContent_diamondPos_subset_relevantSetFinset
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (φ : Proposition Atom)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsf : (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (newForms : List (SignedFormula (Proposition Atom) WorldIndex))
    (hnewForms : (modalApplyOne
        (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
        = RuleResult.linear newForms) :
    successorBirthContent φ₀ b .pos φ w ⊆
      relevantSetFinset φ₀ (newForms ++ b) (modalNextWorld b) := by
  rw [modalApplyOne_diamondPos_mint_fst_S4] at hnewForms
  injection hnewForms with hnewForms
  subst hnewForms
  have hφsub : φ ∈ modalSubfmls φ₀ := by
    have h1 : (Proposition.diamond φ) ∈ modalSubfmls φ₀ := modalUniverseS4_mem_formula (hb _ hsf)
    have h2 : φ ∈ modalSubfmls (Proposition.diamond φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
    exact modalSubfmls_trans_S4 h2 h1
  have hwit : ((Sign.pos, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀ :=
    mem_signedSubfmls_of_formula_S4 .pos hφsub
  intro p hp
  simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨hpmem, hdisj⟩
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hwit, any_beq_of_mem_S4 ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hpmem, any_beq_of_mem_S4 ?_⟩
    rcases hdisj with ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩
    · -- box-positive transmission: p.1 = pos, T(□p.2)@w ∈ b
      have hbmem : (⟨.pos, .box p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hbp : (p.2, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box p.2, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          (boxPositivesOf b).filterMap (fun (ψ, src) =>
            if src == w then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
              if b.any (· == sf') then none else some sf'
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨(p.2, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ htarget))
    · -- diamond-negative transmission: p.1 = neg, F(◇p.2)@w ∈ b
      have hbmem : (⟨.neg, .diamond p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hdedup : b.any (· == (⟨.neg, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          b.filterMap (fun sf' =>
            if sf'.sign == .neg && sf'.label == w then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex :=
                  ⟨.neg, ψ, modalNextWorld b⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨⟨.neg, .diamond p.2, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)

/-! ## Assembling `keyLowerBd`'s Preservation (task 511, Phase 5 continuation) -/

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

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Reusable result-shape-agnostic `keys'` extraction**: whatever `result` turns out to be
(linear/branching/persistent/notApplicable), the 4th tuple component of
`modalStepBranchS4Keyed`'s inner `match result with ...` is always the SAME local `keysLocal`
term (only the first three components vary by branch). This factors out the "case on `result`,
discard everything but the `keys'` component" boilerplate common to all 9
`sf.sign`/`sf.formula` leaves of `modalStepBranchS4_preserves_keyLowerBd`'s assembly, so that
proof only needs to case on `sf.sign`/`sf.formula` (to pin `keysLocal` itself), never on
`result`. -/
private lemma modalStepBranchS4Keyed_result_keys_eq
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

/-- **`keyLowerBd`'s driver-level preservation** (task 511, Phase 5 assembly): every key
recorded after an S4Keyed step remains a lower bound on its live relevant set, over EVERY
branch the step produces. Assembles `modalStepBranchS4Keyed_branch_superset` (handles every
OLD key uniformly, via `relevantSetFinset_mono`, regardless of which rule fired) with the two
closed minting-content subset lemmas (`successorBirthContent_boxNeg_subset_relevantSetFinset`
/ `_diamondPos_subset_relevantSetFinset`, for the NEW key at the two minting leaves). -/
lemma modalStepBranchS4_preserves_keyLowerBd (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hLB : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → k ⊆ relevantSetFinset φ₀ b' w := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b' w :=
    fun b' hb' w k hwk => (hLB w k hwk).trans (relevantSetFinset_mono φ₀ b b' w (hsuper b' hb'))
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmint := modalApplyOne_boxNeg_mint_fst_S4 b acc ψ sf.label
        rw [hresulteq.trans hmint] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_boxNeg_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ hmint
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmint := modalApplyOne_diamondPos_mint_fst_S4 b acc ψ sf.label
        rw [hresulteq.trans hmint] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_diamondPos_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ hmint
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk

omit [Hashable Atom] in
/-- Every `successorBirthContent` value lies in `signedSubfmls φ₀`, provided its witness
formula `φ` is a subformula of `φ₀`: the `insert (s, φ)` component needs
`mem_signedSubfmls_of_formula_S4`, and the filtered remainder is trivially a subset of
`signedSubfmls φ₀` (`Finset.filter_subset`). Reusable by both minting leaves of
`keysInUniverse`'s preservation (unlike the `relevantSetFinset`-targeted subset lemmas above,
this fact needs no information about the POST-step branch at all). -/
private lemma successorBirthContent_subset_signedSubfmls
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) (hφ : φ ∈ modalSubfmls φ₀) :
    successorBirthContent φ₀ b s φ w ⊆ signedSubfmls φ₀ := by
  intro p hp
  simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨hpmem, -⟩
  · exact mem_signedSubfmls_of_formula_S4 s hφ
  · exact hpmem

/-- **`keysInUniverse`'s driver-level preservation** (task 511, Phase 5 assembly): every key
recorded after an S4Keyed step is drawn from `signedSubfmls φ₀`. Unlike `keyLowerBd`, this
obligation is independent of the (possibly several) output branches `newBs` -- it is a fact
about `keys'` alone. Assembled the same way: old keys survive via the `keysInUniverse`
hypothesis directly (`keys ⊆ keys'` always), new keys (the two minting leaves) via
`successorBirthContent_subset_signedSubfmls`, whose witness-formula-membership side
condition is derived exactly as in `successorBirthContent_boxNeg_subset_relevantSetFinset`/
`_diamondPos_subset_relevantSetFinset` above. -/
lemma modalStepBranchS4_preserves_keysInUniverse (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hIU : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ w k, (w, k) ∈ keys' → k ⊆ signedSubfmls φ₀ := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hIU w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.box ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.box ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans_S4 h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .neg ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.diamond ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.diamond ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans_S4 h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .pos ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk

/-! ## Assembling `keysTotal`'s Preservation (task 511, Phase 5 continuation) -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma mem_successorsOf_hasEdge`
(unavailable across files): if `w'` is returned by `acc.successorsOf w`, the edge `w → w'` is
recorded in `acc`. Mirrors `FrameSoundness.lean`'s `mem_successorsOf_hasEdge'`/
`S5Simplification.lean`'s `mem_successorsOf_hasEdge_S5`. Needed to lift the 4-rule's
propagation-target labels (drawn from `acc.successorsOf w`) to `accTargetsKnown`'s edge-indexed
known-worlds form. -/
private lemma mem_successorsOf_hasEdge_S4 {acc : Accessibility} {w w' : WorldIndex}
    (h : w' ∈ acc.successorsOf w) : acc.hasEdge w w' = true := by
  simp only [Accessibility.successorsOf, List.mem_filterMap] at h
  obtain ⟨⟨src, tgt⟩, hmem, heq⟩ := h
  split at heq
  · rename_i hsrc
    simp only [Option.some.injEq] at heq
    simp only [Accessibility.hasEdge, List.any_eq_true, Bool.and_eq_true]
    exact ⟨(src, tgt), hmem, hsrc, by rw [beq_iff_eq]; exact heq⟩
  · simp at heq

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalKnownWorlds_fold_spec`
(unavailable across files), dropping the `Nodup` conjunct this development does not need.
Mirrors `S5Simplification.lean`'s `modalKnownWorlds_fold_spec_S5`. -/
private lemma modalKnownWorlds_fold_spec_S4
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (ws0 : List WorldIndex) :
    ∀ x, x ∈ l.foldl (fun ws sf => if ws.any (· == sf.label) then ws else sf.label :: ws) ws0 ↔
      x ∈ ws0 ∨ ∃ sf ∈ l, sf.label = x := by
  induction l generalizing ws0 with
  | nil => simp
  | cons sf rest ih =>
    by_cases hc : ws0.any (· == sf.label)
    · simp only [List.foldl_cons, if_pos hc]
      intro x
      rw [ih ws0]
      have hmemws0 : sf.label ∈ ws0 := by simpa [List.any_eq_true] using hc
      constructor
      · rintro (h | ⟨sf', hsf', rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨sf', List.mem_cons_of_mem _ hsf', rfl⟩
      · rintro (h | ⟨sf', hsf', hfeq⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hsf' with rfl | hsf'
          · exact Or.inl (hfeq ▸ hmemws0)
          · exact Or.inr ⟨sf', hsf', hfeq⟩
    · simp only [List.foldl_cons, if_neg hc]
      intro x
      rw [ih (sf.label :: ws0)]
      constructor
      · rintro (h | ⟨sf', hsf', rfl⟩)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr ⟨sf, List.mem_cons_self, rfl⟩
          · exact Or.inl h
        · exact Or.inr ⟨sf', List.mem_cons_of_mem _ hsf', rfl⟩
      · rintro (h | ⟨sf', hsf', hfeq⟩)
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp hsf' with rfl | hsf'
          · exact Or.inl (hfeq ▸ List.mem_cons_self)
          · exact Or.inr ⟨sf', hsf', hfeq⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma mem_modalKnownWorlds`
(unavailable across files). Mirrors `S5Simplification.lean`'s `mem_modalKnownWorlds_S5`. -/
private lemma mem_modalKnownWorlds_S4
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (x : WorldIndex) :
    x ∈ modalKnownWorlds l ↔ ∃ sf ∈ l, sf.label = x := by
  unfold modalKnownWorlds
  simpa using modalKnownWorlds_fold_spec_S4 l [] x

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalKnownWorlds_mono_append`
(unavailable across files): appending formulas to the front of a branch only grows its
known-worlds set. Mirrors `S5Simplification.lean`'s `modalKnownWorlds_mono_append_S5`. -/
private lemma modalKnownWorlds_mono_append_S4
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    ∀ x ∈ modalKnownWorlds b, x ∈ modalKnownWorlds (xs ++ b) := by
  intro x hx
  rw [mem_modalKnownWorlds_S4] at hx ⊢
  obtain ⟨sf, hsf, rfl⟩ := hx
  exact ⟨sf, List.mem_append_right _ hsf, rfl⟩

omit [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma mintGroup_label_eq_freshWorld`
(unavailable across files): the K minting groups (`boxNeg`'s and `diamondPos`'s live shape)
always emit formulas entirely labeled at the fresh witness `modalNextWorld b`, since the
witness, `boxProps`, and `diaNegProps` are all constructed at that one fresh label. -/
private lemma mintGroup_label_eq_freshWorld_S4
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

/-- The S4-augmented rule `modalApplyOneS4Rules` never mints at its two T/4-relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): composes `modalApplyOneT_boxPos_diaNeg_known_S4` (K+T layer) with the
4-rule propagation (`modalFourBoxProp`/`modalFourDiaNegProp`), whose targets are recorded
successors of `w` -- known via `accTargetsKnown` composed with `mem_successorsOf_hasEdge_S4`. -/
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
        exact hknown w w' (mem_successorsOf_hasEdge_S4 hw')
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
        exact hknown w w' (mem_successorsOf_hasEdge_S4 hw')
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
      rw [hzlabel, mem_modalKnownWorlds_S4]; exact ⟨sf, hsfmem, rfl⟩
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨-, hzlabel⟩ := hprop z hz
      rw [hzlabel, mem_modalKnownWorlds_S4]; exact ⟨sf, hsfmem, rfl⟩
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨-, hzlabel⟩ := hprop z hz
      rw [hzlabel, mem_modalKnownWorlds_S4]; exact ⟨sf, hsfmem, rfl⟩
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
private lemma modalApplyOneS4Keyed_nonMint_known_S4
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

/-! ## Non-Minting Universe-Membership Composite (task 511, Phase 6 groundwork for `bClosure`)

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
private lemma modalApplyOne_boxPos_snd_S4
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
private lemma modalApplyOne_diamondNeg_snd_S4
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
        hknown w x.label (mem_successorsOf_hasEdge_S4 hxl)
      obtain ⟨sf', hsf'mem, hsf'lab⟩ := (mem_modalKnownWorlds_S4 b x.label).mp hxlk
      have hbound : sf'.label ≤ modalWorldBoundS4 φ₀ := modalUniverseS4_mem_label (hb sf' hsf'mem)
      rw [hsf'lab] at hbound
      exact mem_modalUniverseS4_of' hbound (modalSubfmls_trans_S4 hxf hsrc)
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
        exact mem_modalUniverseS4_of' hbound (modalSubfmls_trans_S4 (by simp [modalSubfmls]) hsrc)
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
        hknown w x.label (mem_successorsOf_hasEdge_S4 hxl)
      obtain ⟨sf', hsf'mem, hsf'lab⟩ := (mem_modalKnownWorlds_S4 b x.label).mp hxlk
      have hbound : sf'.label ≤ modalWorldBoundS4 φ₀ := modalUniverseS4_mem_label (hb sf' hsf'mem)
      rw [hsf'lab] at hbound
      exact mem_modalUniverseS4_of' hbound (modalSubfmls_trans_S4 hxf hsrc)
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
        exact mem_modalUniverseS4_of' hbound (modalSubfmls_trans_S4 (by simp [modalSubfmls]) hsrc)
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
        have hxlk : w' ∈ modalKnownWorlds b := hknown w w' (mem_successorsOf_hasEdge_S4 hw')
        obtain ⟨sf', hsf'mem, hsf'lab⟩ := (mem_modalKnownWorlds_S4 b w').mp hxlk
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
        have hxlk : w' ∈ modalKnownWorlds b := hknown w w' (mem_successorsOf_hasEdge_S4 hw')
        obtain ⟨sf', hsf'mem, hsf'lab⟩ := (mem_modalKnownWorlds_S4 b w').mp hxlk
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

/-- Outside the two K-minting shapes, and with `sf.formula` non-modal, every emitted formula
lands in `modalUniverseS4 φ₀`: `modalApplyOne_prop_outputs_subset` gives formula ∈
`modalSubfmls sf.formula` at the unchanged label `sf.label`, composed with `hb`'s own bound on
`sf` via `modalSubfmls_trans_S4`. Universe-membership analog of `modalApplyOne_nonModal_known_S4`. -/
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
        (modalSubfmls_trans_S4 hzf (modalUniverseS4_mem_formula hsfbound))
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzf, hzlabel⟩ := hprop z hz
      exact mem_modalUniverseS4_of' (hzlabel ▸ modalUniverseS4_mem_label hsfbound)
        (modalSubfmls_trans_S4 hzf (modalUniverseS4_mem_formula hsfbound))
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzf, hzlabel⟩ := hprop z hz
      exact mem_modalUniverseS4_of' (hzlabel ▸ modalUniverseS4_mem_label hsfbound)
        (modalSubfmls_trans_S4 hzf (modalUniverseS4_mem_formula hsfbound))
    · rw [hpr] at hpa; simp [RuleResult.isApplicable] at hpa
  · rw [if_neg hpa]
    rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
      simp_all

/-- **Composite non-mint universe-membership fact for `modalApplyOneS4Keyed`**: at any signed
formula outside the two minting shapes, every emitted formula lands in `modalUniverseS4 φ₀`.
Universe-membership analog of `modalApplyOneS4Keyed_nonMint_known_S4`, exactly the fact
`bClosure`'s preservation needs at its 12 non-minting `sf.sign`/`sf.formula` leaves. -/
private lemma modalApplyOneS4Keyed_nonMint_universe_S4
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
private lemma modalStepBranchS4Keyed_keys_subset
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
    simp only [hs, hf]
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

/-- **`keysTotal`'s driver-level preservation** (task 511, Phase 5 assembly, the crux): every
known world after an S4Keyed step has a recorded key. Assembled by a top-level split on whether
`sf` is one of the two minting shapes: at the 2 minting shapes, the newly-minted world's label
is exactly `modalNextWorld b` (`mintGroup_label_eq_freshWorld_S4`), which `keys'` gains an entry
for by construction; at the other 12 shapes, `modalApplyOneS4Keyed_nonMint_known_S4` shows no
label beyond `modalKnownWorlds b` is ever introduced, so the new-known-world case never
actually arises there and old keys (`keys ⊆ keys'`, `modalStepBranchS4Keyed_keys_subset`)
suffice. -/
lemma modalStepBranchS4_preserves_keysTotal (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ keys' := by
  have hkeysub := modalStepBranchS4Keyed_keys_subset φ₀ b e acc keys newBs newExps newAcc keys'
    hstep
  have hold : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys' :=
    fun w hw => (hKT w hw).imp (fun k hk => hkeysub hk)
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintfst := modalApplyOne_boxNeg_mint_fst_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans hmintfst
        have hlabel := mintGroup_label_eq_freshWorld_S4 b sf.label .neg ψ
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .neg ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds_S4] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · have hlabeleq := hlabel sf' hsf'new
          rw [hlabeleq, hkeq2]
          exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
            List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds_S4]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintfst := modalApplyOne_diamondPos_mint_fst_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans hmintfst
        have hlabel := mintGroup_label_eq_freshWorld_S4 b sf.label .pos ψ
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .pos ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds_S4] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · have hlabeleq := hlabel sf' hsf'new
          rw [hlabeleq, hkeq2]
          exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
            List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds_S4]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' w hw
    have hwb : w ∈ modalKnownWorlds b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds_S4] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds_S4]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        rw [mem_modalKnownWorlds_S4] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' (List.mem_flatten.mpr ⟨br, hbr, hsf'⟩)
        · rw [mem_modalKnownWorlds_S4]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds_S4] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds_S4]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf; simp at hsf
    exact hold w hwb

/-- **`keysDistinct`'s driver-level preservation** (task 511, Phase 5 assembly): every pair of
distinctly-labeled keys recorded after an S4Keyed step remains distinct-keyed. Assembled the
same way as `keyLowerBd`/`keysInUniverse`/`keysTotal`: a `sf.sign`/`sf.formula` case split via
`modalStepBranchS4Keyed_result_keys_eq`, 12 leaves trivial (`keys' = keys`), the 2 minting
leaves reduce to exactly `keysUpdate_preserves_keysDistinct`'s own match shape. -/
lemma modalStepBranchS4_preserves_keysDistinct (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ w1 w2 k1 k2, (w1, k1) ∈ keys' → (w2, k2) ∈ keys' → w1 ≠ w2 → k1 ≠ k2 := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w1 w2 k1 k2 h1 h2 hne
  rw [hkeq] at h1 h2
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at h1 h2
  all_goals first
    | exact hKD w1 w2 k1 k2 h1 h2 hne
    | skip
  case neg.neg.box =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .neg ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne
  case neg.pos.diamond =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .pos ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne

/-- **Composite `.snd = acc` fact for `modalApplyOneS4Keyed`'s 12 non-minting leaves**: mirrors
`modalApplyOneS4Keyed_nonMint_known_S4`'s exact case-split (same three underlying pieces --
`modalApplyOneS4Rules_boxPos_diaNeg_known_S4`/`modalApplyOne_nonModal_known_S4`, both of which
also supply `.snd = acc`), extracting the accessibility-unchanged half instead of the
known-worlds half. Needed for `accFresh`/`accKnown`/`outDegEq`'s preservation at the 12
non-minting shapes: `acc` is untouched there, so those three invariants (none of which depend on
`e`/`b` beyond `acc` itself, or trivially so) carry over for free. -/
private lemma modalApplyOneS4Keyed_nonMint_snd_eq_acc
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

/-- **`eNodup`'s driver-level preservation**: `modalStepBranchS4Keyed` preserves `Nodup`-ness of
the expanded set `e`, exactly like the generic `modalStepBranch_preserves_expandedNodup_gen`
(`FmpMeasure.lean`) -- fully rule-agnostic, only the top-level `RuleResult` constructor shape
matters, `keys`/`keys'` never enter the argument. Direct case split on `result` (not routed
through the generic lemma, since `modalStepBranchS4Keyed` returns a 4-tuple with `keys'` bolted
on rather than literally being `modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys)`). -/
lemma modalStepBranchS4_preserves_eNodup (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys'))
    (hnodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfnotmem : sf ∉ e := by
    intro hmem
    exact hexp (by simp only [List.any_eq_true]; exact ⟨sf, hmem, by simp⟩)
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact hnodup
  · rw [hres] at hsf; simp at hsf

omit [DecidableEq Atom] [Hashable Atom] in
/-- `outDeg` under `addEdge` at the matching source: local re-derivation of `FmpMeasure.lean`'s
`private lemma outDeg_addEdge_self` (unavailable across files). -/
private lemma outDeg_addEdge_self_S4 (acc : Accessibility) (w wf : WorldIndex) :
    outDeg (acc.addEdge w wf) w = outDeg acc w + 1 := by
  simp [outDeg, Accessibility.successorsOf, Accessibility.addEdge]

omit [DecidableEq Atom] [Hashable Atom] in
/-- `outDeg` under `addEdge` is unchanged at any world other than the edge's source: local
re-derivation of `FmpMeasure.lean`'s `private lemma outDeg_addEdge_ne` (unavailable across
files). -/
private lemma outDeg_addEdge_ne_S4 (acc : Accessibility) (w wf w' : WorldIndex) (h : w' ≠ w) :
    outDeg (acc.addEdge w wf) w' = outDeg acc w' := by
  simp only [outDeg, Accessibility.successorsOf, Accessibility.addEdge, List.filterMap_cons]
  have : (w == w') = false := by simp only [beq_eq_false_iff_ne]; exact fun heq => h heq.symm
  simp [this]

/-- **`keysWorldsKnown`, a proof-internal auxiliary invariant** (not an `S4LoopInv` field: adding
one would reopen the already-`[COMPLETED]` Phase 4 struct design): every RECORDED key's world is
already a known world of the branch. Not literally implied by any single `S4LoopInv` field
(`keysTotal` only gives the converse direction), but true by construction -- `keys` only ever
gains an entry `(modalNextWorld b, ...)` in the SAME step that mints the branch formula carrying
that exact label, so the keyed world is known from the moment its key is recorded onward. Needed
by `accFresh`/`accKnown`'s preservation, whose guard-BLOCKED minting sub-case adds an edge to
`blockingWorldS4Keyed`'s result `wBlock` -- a RECORDED-key world, not necessarily K's usual
"freshly-minted" witness, so the standard `hFreshLocal`-style dichotomy (nonempty `.linear`
headed by the fresh witness) does not apply; `wBlock ∈ modalKnownWorlds b` is what closes the
gap instead. Threaded as an extra hypothesis/conclusion alongside `S4LoopInv` at every call site
(including the final assembly), exactly like `RuleApplicationSpec`-style raw hypotheses
elsewhere in this development. -/
lemma modalStepBranchS4_preserves_keysWorldsKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b' := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b' := by
    intro b' hb' w k hwk
    obtain ⟨sf', hsf', hlab⟩ := (mem_modalKnownWorlds_S4 b w).mp (hKW w k hwk)
    exact (mem_modalKnownWorlds_S4 b' w).mpr ⟨sf', hsuper b' hb' sf' hsf', hlab⟩
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans (modalApplyOne_boxNeg_mint_fst_S4 b acc ψ sf.label)
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds_S4]
        exact ⟨⟨.neg, ψ, modalNextWorld b⟩, List.mem_append_left _ List.mem_cons_self, rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans (modalApplyOne_diamondPos_mint_fst_S4 b acc ψ sf.label)
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds_S4]
        exact ⟨⟨.pos, ψ, modalNextWorld b⟩, List.mem_append_left _ List.mem_cons_self, rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-- **`outDegEq`'s driver-level preservation**: the out-degree/expanded-set correspondence
survives an S4Keyed step, for every branch it produces. At the 12 non-minting shapes, `acc` is
literally unchanged (`modalApplyOneS4Keyed_nonMint_snd_eq_acc`) and `sf` is not minting-shaped,
so appending it to `e` (when the result is `.linear`/`.branching`) does not perturb the filtered
count. At the 2 minting shapes' UNBLOCKED sub-case, `modalApplyOneS4Keyed` reduces to plain K's
`modalApplyOne`, so K's own per-call obligation `modalApplyOne_outDeg_step` (`FmpMeasure.lean`,
public) applies directly. At the BLOCKED sub-case, `newAcc = acc.addEdge sf.label wBlock` --
`outDeg`'s bookkeeping is insensitive to whether the edge's target `wBlock` is a genuinely fresh
witness or a recorded-key world, so the identical `outDeg_addEdge_self_S4`/`_ne_S4` argument K's
own minting case uses applies verbatim (no `keysWorldsKnown` dependency here, unlike
`accFresh`/`accKnown`). -/
lemma modalStepBranchS4_preserves_outDegEq (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (houtdeg : ∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ e' ∈ newExps, ∀ w, outDeg newAcc w =
      (e'.filter (fun x => x.label == w && isMintingShaped x)).length := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      have hmshape : isMintingShaped sf = true := by rw [hsfeq]; rfl
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hstep2 := modalApplyOne_outDeg_step (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b e acc houtdeg
        rw [← hpaireq] at hstep2
        dsimp only at hstep2
        rcases hres : result with nf | brs | nf | -
        · rw [hres] at hsf hstep2
          dsimp only at hstep2
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨-, rfl, rfl, -⟩ := hsf
          intro e' he' w
          simp only [List.mem_singleton] at he'
          subst he'
          rw [hsfeq]
          exact hstep2 w
        · rw [hres] at hsf hstep2
          dsimp only at hstep2
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨-, rfl, rfl, -⟩ := hsf
          intro e' he' w
          obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
          rw [hsfeq]
          exact hstep2 w
        · rw [hres] at hsf hstep2
          dsimp only at hstep2
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨-, rfl, rfl, -⟩ := hsf
          intro e' he' w
          simp only [List.mem_singleton] at he'
          subst he'
          exact hstep2 w
        · rw [hres] at hsf; simp at hsf
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨-, rfl, rfl, -⟩ := hsf
        intro e' he' w
        simp only [List.mem_singleton] at he'
        subst he'
        rcases eq_or_ne w sf.label with hw | hw
        · rw [hw, outDeg_addEdge_self_S4, houtdeg sf.label, List.filter_append,
            List.length_append]
          simp [List.filter_cons, hmshape]
        · rw [outDeg_addEdge_ne_S4 acc sf.label wBlock w hw, houtdeg w,
            List.filter_append, List.length_append]
          have hne : (sf.label == w) = false := by simpa using (Ne.symm hw)
          simp [List.filter_cons, hne]
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      have hmshape : isMintingShaped sf = true := by rw [hsfeq]; rfl
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hstep2 := modalApplyOne_outDeg_step (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b e acc houtdeg
        rw [← hpaireq] at hstep2
        dsimp only at hstep2
        rcases hres : result with nf | brs | nf | -
        · rw [hres] at hsf hstep2
          dsimp only at hstep2
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨-, rfl, rfl, -⟩ := hsf
          intro e' he' w
          simp only [List.mem_singleton] at he'
          subst he'
          rw [hsfeq]
          exact hstep2 w
        · rw [hres] at hsf hstep2
          dsimp only at hstep2
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨-, rfl, rfl, -⟩ := hsf
          intro e' he' w
          obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
          rw [hsfeq]
          exact hstep2 w
        · rw [hres] at hsf hstep2
          dsimp only at hstep2
          simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨-, rfl, rfl, -⟩ := hsf
          intro e' he' w
          simp only [List.mem_singleton] at he'
          subst he'
          exact hstep2 w
        · rw [hres] at hsf; simp at hsf
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨-, rfl, rfl, -⟩ := hsf
        intro e' he' w
        simp only [List.mem_singleton] at he'
        subst he'
        rcases eq_or_ne w sf.label with hw | hw
        · rw [hw, outDeg_addEdge_self_S4, houtdeg sf.label, List.filter_append,
            List.length_append]
          simp [List.filter_cons, hmshape]
        · rw [outDeg_addEdge_ne_S4 acc sf.label wBlock w hw, houtdeg w,
            List.filter_append, List.length_append]
          have hne : (sf.label == w) = false := by simpa using (Ne.symm hw)
          simp [List.filter_cons, hne]
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm : isMintingShaped sf = false := by
      unfold isMintingShaped
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
        simp_all
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨-, rfl, rfl, -⟩ := hsf
      intro e' he' w
      simp only [List.mem_singleton] at he'
      subst he'
      rw [houtdeg w, List.filter_append, List.length_append]
      simp [List.filter_cons, hnm]
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨-, rfl, rfl, -⟩ := hsf
      intro e' he' w
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
      rw [houtdeg w, List.filter_append, List.length_append]
      simp [List.filter_cons, hnm]
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨-, rfl, rfl, -⟩ := hsf
      intro e' he' w
      simp only [List.mem_singleton] at he'
      subst he'
      exact houtdeg w
    · rw [hres] at hsf; simp at hsf

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `Soundness.lean`'s `private lemma accFreshInv_append` (unavailable
across files): prepending formulas to a branch preserves `accFreshInv`. -/
private lemma accFreshInv_append_S4
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (hInv : accFreshInv b acc)
    (xs : List (SignedFormula (Proposition Atom) WorldIndex)) :
    accFreshInv (xs ++ b) acc := by
  intro w w' hedge
  obtain ⟨hw, hw'⟩ := hInv w w' hedge
  exact ⟨Nat.lt_of_lt_of_le hw (modalNextWorld_le_append xs b),
         Nat.lt_of_lt_of_le hw' (modalNextWorld_le_append xs b)⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `Soundness.lean`'s `private lemma hasEdge_addEdge_cases` (unavailable
across files): decompose membership of an edge in `acc.addEdge w w'`. -/
private lemma hasEdge_addEdge_cases_S4 {acc : Accessibility} {w w' a a' : WorldIndex}
    (h : (acc.addEdge w w').hasEdge a a' = true) :
    (a = w ∧ a' = w') ∨ acc.hasEdge a a' = true := by
  simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hw, hw'⟩ | h
  · exact Or.inl ⟨hw.symm, hw'.symm⟩
  · exact Or.inr h

/-- **`accFresh`'s driver-level preservation**: the per-branch freshness invariant `accFreshInv`
survives an S4Keyed step. At the 12 non-minting shapes, `acc` is unchanged
(`modalApplyOneS4Keyed_nonMint_snd_eq_acc`) and every produced branch is a prepend of `b`, so
`accFreshInv_append_S4` carries the invariant forward directly. At the 2 minting shapes'
UNBLOCKED sub-case, `modalApplyOneS4Keyed` reduces to plain K's `modalApplyOne`, whose unique new
edge targets the genuinely fresh witness `modalNextWorld b` -- the standard K freshness argument
applies. At the BLOCKED sub-case the new edge targets `wBlock` instead -- NOT necessarily fresh,
so `keysWorldsKnown` (`wBlock ∈ modalKnownWorlds b`, hence `wBlock < modalNextWorld b` via
`modalNextWorld_gt`) is what bounds it, in place of the standard freshness argument. -/
lemma modalStepBranchS4_preserves_accFresh (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hFresh : accFreshInv b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans (modalApplyOne_boxNeg_mint_fst_S4 b acc ψ sf.label)
        have hsndeq := haccnew0.trans (modalApplyOne_boxNeg_mint_snd_S4 b acc ψ sf.label)
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases_S4 hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.neg, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex) (List.mem_append_left _
              List.mem_cons_self)⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases_S4 hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds_S4 b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans (modalApplyOne_diamondPos_mint_fst_S4 b acc ψ sf.label)
        have hsndeq := haccnew0.trans (modalApplyOne_diamondPos_mint_snd_S4 b acc ψ sf.label)
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases_S4 hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.pos, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex) (List.mem_append_left _
              List.mem_cons_self)⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases_S4 hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds_S4 b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      exact accFreshInv_append_S4 hFresh x
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf; simp at hsf

/-- **`accKnown`'s driver-level preservation**: every `acc`-edge target stays a known branch
world across an S4Keyed step. Mirrors `accFresh`'s case split exactly (same three regimes,
same `keysWorldsKnown` dependency at the BLOCKED sub-case), but concludes membership in
`modalKnownWorlds b'` rather than a numeric bound, via `modalKnownWorlds_mono_append_S4` to lift
old facts across a branch prepend. -/
lemma modalStepBranchS4_preserves_accKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans (modalApplyOne_boxNeg_mint_fst_S4 b acc ψ sf.label)
        have hsndeq := haccnew0.trans (modalApplyOne_boxNeg_mint_snd_S4 b acc ψ sf.label)
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases_S4 hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds_S4]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩, List.mem_append_left _ List.mem_cons_self, rfl⟩
        · exact modalKnownWorlds_mono_append_S4 _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases_S4 hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
            hblock)
        · exact hknown w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOne (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans (modalApplyOne_diamondPos_mint_fst_S4 b acc ψ sf.label)
        have hsndeq := haccnew0.trans (modalApplyOne_diamondPos_mint_snd_S4 b acc ψ sf.label)
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases_S4 hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds_S4]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩, List.mem_append_left _ List.mem_cons_self, rfl⟩
        · exact modalKnownWorlds_mono_append_S4 _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases_S4 hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
            hblock)
        · exact hknown w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append_S4 _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append_S4 _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append_S4 _ b _ (hknown w w' hedge)
    · rw [hres] at hsf; simp at hsf

/-! ## S4 Hintikka Set -/

/-- A modal S4 Hintikka set: the S4 analogue of `modalHintikkaSet` (Saturation.lean),
with `modalApplyOne` replaced by `modalApplyOneS4 φ₀` in conjunct 2 (Decision D3).
Conjuncts 1, 3, 4 are unchanged and apply-agnostic:

1. The branch is not closed.
2. Every non-minting-shaped formula's `modalApplyOneS4 φ₀` output is already present on
   the branch (the saturation condition, now stated against the S4 rule set: K + T + 4 +
   the minting guard).
3. Box-negative witness: `F(□φ)@w ∈ b` implies some successor `w'` of `w` has `F(φ)@w' ∈ b`.
4. Diamond-positive witness: `T(◇φ)@w ∈ b` implies some successor `w'` of `w` has
   `T(φ)@w' ∈ b`.

Conjuncts 3/4 are existential over successors, and a **loop-back edge satisfies them
natively** (Decision D3): this is the favourable accident that makes equality-blocking
compatible with the Hintikka characterization without any change to its shape. Per Decision
D4, this predicate is consumed as a *hypothesis* by the bridge lemmas in this file (not
proved from the driver here) -- `modalExpandBranchesS4_hintikka` (Phase 9, 510-gated) is
where a completed S4 tableau's open branch is shown to satisfy it. -/
def modalHintikkaSetS4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  isModalClosed b = false ∧
  (∀ sf ∈ b,
    let (result, _) := modalApplyOneS4 φ₀ sf b acc
    match sf.sign, sf.formula with
    | .neg, .box _ => True    -- F(□φ): minting-guarded rule; handled by conjunct 3
    | .pos, .diamond _ => True  -- T(◇φ): minting-guarded rule; handled by conjunct 4
    | _, _ =>
      match result with
      | .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b
      | .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .notApplicable => True) ∧
  -- Box-negative witness: F(□φ)@w on the branch implies a successor world with F(φ)
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.neg, .box φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.neg, φ, w'⟩ ∈ b) ∧
  -- Diamond-positive witness: T(◇φ)@w on the branch implies a successor world with T(φ)
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.pos, .diamond φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.pos, φ, w'⟩ ∈ b)

/-- **Bridge (task 511, Phase 7)**: `modalHintikkaSetS4 φ₀` is exactly `modalHintikkaSetGen
(modalApplyOneS4 φ₀)`. Closes by `rfl` (mirrors `Saturation.lean`'s `modalHintikkaSet_eq`),
confirming the substitution in `modalHintikkaSetGen` is faithful for the S4 rule set. Lets a
generic-driver conclusion about `modalApplyOneS4 φ₀` be recovered in the concrete
`modalHintikkaSetS4` form (or vice versa) without unfolding either definition. -/
theorem modalHintikkaSetS4_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalHintikkaSetS4 φ₀ b acc = modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc := rfl

/-! ## S4 Hintikka Bridges -/

/-- Bridge from `acc.hasEdge` to `Accessibility.successorsOf` membership: the converse of
`FrameSoundness.lean`'s `mem_successorsOf_hasEdge'`. Local mirror of the same fact proved
(privately) in `FmpMeasure.lean` and `Completeness.lean`'s bridge lemmas' inline proofs. -/
private lemma hasEdge_mem_successorsOf {acc : Accessibility} {w w' : WorldIndex}
    (hr : acc.hasEdge w w' = true) : w' ∈ acc.successorsOf w := by
  simp only [Accessibility.successorsOf, List.mem_filterMap]
  simp only [Accessibility.hasEdge, List.any_eq_true] at hr
  obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
  exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩

/-- The single-edge 4-rule bridge: `modalHintikkaSetS4 φ₀ b acc`, `T(□ψ)@w ∈ b`,
`acc.hasEdge w w' = true` imply `T(□ψ)@w' ∈ b` -- the box formula *itself* survives across
one recorded edge. This is the S4-specific content that makes the crux bridge
(`hintikkaS4_box_pos_reflTransGen` below) possible: the induction it drives carries
`T(□ψ)@·`, not `T(ψ)@·`.

Proof shape mirrors `hintikka_box_pos` (`Completeness.lean`) one layer further down: unfold
`modalApplyOneS4` at this (non-minting) shape through `modalApplyOneS4Rules`,
`modalApplyOneT`, and `modalApplyOne` in turn (`htR`, `hk`), then show the target formula
survives every merge/filter layer whenever it is not already on the branch -- it is always
in `modalFourBoxProp`'s output (`htarget_mem_fourNew`), and a generic two-case argument
(`hmem_merge`: either already in the front list, or survives the filter against it) shows it
lands in the final merged list regardless of what the K/T layers themselves produced. -/
lemma hintikkaS4_box_pos_step
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : acc.hasEdge w w' = true) :
    (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.pos, .box ψ, w⟩ hmem
  simp only at hcond
  have hshape : modalApplyOneS4 φ₀ ⟨.pos, .box ψ, w⟩ b acc =
      modalApplyOneS4Rules ⟨.pos, .box ψ, w⟩ b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  have hw'succ : w' ∈ acc.successorsOf w := hasEdge_mem_successorsOf hr
  by_cases hinb :
      (b.any fun x => x == (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
        = true
  · simp only [List.any_eq_true, beq_iff_eq] at hinb
    obtain ⟨sf', hsf'mem, rfl⟩ := hinb
    exact hsf'mem
  · have htarget_mem_fourNew :
        (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          modalFourBoxProp b acc ψ w := by
      simp only [modalFourBoxProp, List.mem_filterMap]
      exact ⟨w', hw'succ, if_neg hinb⟩
    have htR :
        (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        (match (modalApplyOne (⟨.pos, .box ψ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTBoxSelf b ψ w)
          | other => other) := by
      unfold modalApplyOneT
      obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc
      cases kResult <;> first | rfl | (simp only []; split <;> rfl)
    have hk :
        (modalApplyOne (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (boxPropagation b acc ψ w) := by
      unfold modalApplyOne
      simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
        modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
      split_ifs <;> simp_all
    rw [hk] at htR
    rw [htR] at hcond
    have hfourNotEmpty : ¬ (modalFourBoxProp b acc ψ w).isEmpty = true := by
      have hne : (modalFourBoxProp b acc ψ w).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, htarget_mem_fourNew⟩
      simp [hne]
    simp only [if_neg hfourNotEmpty] at hcond
    have hmem_merge : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex)),
        (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          l ++ (modalFourBoxProp b acc ψ w).filter (fun x => !(l.any (· == x))) := by
      intro l
      by_cases hinl :
          (l.any fun x => x == (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
            = true
      · simp only [List.any_eq_true, beq_iff_eq] at hinl
        obtain ⟨sf', hsf'mem, rfl⟩ := hinl
        exact List.mem_append_left _ hsf'mem
      · refine List.mem_append_right _ ?_
        simp only [List.mem_filter]
        exact ⟨htarget_mem_fourNew, by simp [hinl]⟩
    split_ifs at hcond with h1 h2
    · exact hcond _ htarget_mem_fourNew
    · exact hcond _ (hmem_merge _)
    · exact hcond _ (hmem_merge _)
    · exact hcond _ (hmem_merge _)

/-- Dual of `hintikkaS4_box_pos_step` for the diamond-negative shape: `modalHintikkaSetS4
φ₀ b acc`, `F(◇ψ)@w ∈ b`, `acc.hasEdge w w' = true` imply `F(◇ψ)@w' ∈ b` -- the diamond
formula itself survives across one recorded edge. Proof is the exact mirror of
`hintikkaS4_box_pos_step`, with `.pos, .box` / `modalTBoxSelf` / `modalFourBoxProp` replaced
by `.neg, .diamond` / `modalTDiaNegSelf` / `modalFourDiaNegProp` throughout; K's diamondNeg
arm computes its propagation list inline (no named `boxPropagation`-style helper exists for
it), so the `hk` step restates that inline computation directly. -/
lemma hintikkaS4_dia_neg_step
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : acc.hasEdge w w' = true) :
    (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.neg, .diamond ψ, w⟩ hmem
  simp only at hcond
  have hshape : modalApplyOneS4 φ₀ ⟨.neg, .diamond ψ, w⟩ b acc =
      modalApplyOneS4Rules ⟨.neg, .diamond ψ, w⟩ b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  have hw'succ : w' ∈ acc.successorsOf w := hasEdge_mem_successorsOf hr
  by_cases hinb :
      (b.any fun x => x == (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
        = true
  · simp only [List.any_eq_true, beq_iff_eq] at hinb
    obtain ⟨sf', hsf'mem, rfl⟩ := hinb
    exact hsf'mem
  · have htarget_mem_fourNew :
        (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          modalFourDiaNegProp b acc ψ w := by
      simp only [modalFourDiaNegProp, List.mem_filterMap]
      exact ⟨w', hw'succ, if_neg hinb⟩
    have htR :
        (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        (match (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTDiaNegSelf b ψ w)
          | other => other) := by
      unfold modalApplyOneT
      obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc
      cases kResult <;> first | rfl | (simp only []; split <;> rfl)
    have hk :
        (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
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
    rw [hk] at htR
    rw [htR] at hcond
    have hfourNotEmpty : ¬ (modalFourDiaNegProp b acc ψ w).isEmpty = true := by
      have hne : (modalFourDiaNegProp b acc ψ w).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, htarget_mem_fourNew⟩
      simp [hne]
    simp only [if_neg hfourNotEmpty] at hcond
    have hmem_merge : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex)),
        (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          l ++ (modalFourDiaNegProp b acc ψ w).filter (fun x => !(l.any (· == x))) := by
      intro l
      by_cases hinl :
          (l.any fun x =>
              x == (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
            = true
      · simp only [List.any_eq_true, beq_iff_eq] at hinl
        obtain ⟨sf', hsf'mem, rfl⟩ := hinl
        exact List.mem_append_left _ hsf'mem
      · refine List.mem_append_right _ ?_
        simp only [List.mem_filter]
        exact ⟨htarget_mem_fourNew, by simp [hinl]⟩
    split_ifs at hcond with h1 h2
    · exact hcond _ htarget_mem_fourNew
    · exact hcond _ (hmem_merge _)
    · exact hcond _ (hmem_merge _)
    · exact hcond _ (hmem_merge _)

/-- The T-rule endpoint of the box-positive chain: `T(□ψ)@w ∈ b` implies `T(ψ)@w ∈ b`
(same world, via the T self-propagation arm `modalTBoxSelf` inherited through
`modalApplyOneT`). Combined with `hintikkaS4_box_pos_step`, this is exactly the two
ingredients `hintikkaS4_box_pos_reflTransGen`'s induction needs: `step` carries `T(□ψ)@·`
across each edge, and `self` discharges the endpoint (including the reflexive `w = w'` base
case) into `T(ψ)@·`. -/
lemma hintikkaS4_box_pos_self
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.pos, .box ψ, w⟩ hmem
  simp only at hcond
  have hshape : modalApplyOneS4 φ₀ ⟨.pos, .box ψ, w⟩ b acc =
      modalApplyOneS4Rules ⟨.pos, .box ψ, w⟩ b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  by_cases hinb :
      (b.any fun x => x == (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
  · simp only [List.any_eq_true, beq_iff_eq] at hinb
    obtain ⟨sf', hsf'mem, rfl⟩ := hinb
    exact hsf'mem
  · have htarget_mem_self :
        (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalTBoxSelf b ψ w := by
      unfold modalTBoxSelf
      simp [hinb]
    have htR :
        (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        (match (modalApplyOne (⟨.pos, .box ψ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTBoxSelf b ψ w)
          | other => other) := by
      unfold modalApplyOneT
      obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc
      cases kResult <;> first | rfl | (simp only []; split <;> rfl)
    have hk :
        (modalApplyOne (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (boxPropagation b acc ψ w) := by
      unfold modalApplyOne
      simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
        modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
      split_ifs <;> simp_all
    rw [hk] at htR
    rw [htR] at hcond
    have hselfNotEmpty : ¬ (modalTBoxSelf b ψ w).isEmpty = true := by
      have hne : (modalTBoxSelf b ψ w).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, htarget_mem_self⟩
      simp [hne]
    simp only [if_neg hselfNotEmpty] at hcond
    have hmem_merge : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex)),
        (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          l ++ (modalTBoxSelf b ψ w).filter (fun x => !(l.any (· == x))) := by
      intro l
      by_cases hinl :
          (l.any fun x => x == (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
            = true
      · simp only [List.any_eq_true, beq_iff_eq] at hinl
        obtain ⟨sf', hsf'mem, rfl⟩ := hinl
        exact List.mem_append_left _ hsf'mem
      · refine List.mem_append_right _ ?_
        simp only [List.mem_filter]
        exact ⟨htarget_mem_self, by simp [hinl]⟩
    -- The 4-rule layer (S4Rules) merges the T-layer's result with the box-itself
    -- propagation `modalFourBoxProp`, filtered against whatever the T-layer produced.
    -- `w`'s target `T(ψ)@w` (unwrapped body) is untouched by that filter's *content*, since
    -- it already sits inside the T-layer's own list; only its position in the final
    -- concatenation changes.
    split_ifs at hcond with h1 <;> simp only at hcond
    · exact hcond _ (List.mem_append_left _ htarget_mem_self)
    · exact hcond _ (List.mem_append_left _ htarget_mem_self)
    · exact hcond _ (List.mem_append_left _ (hmem_merge _))
    · exact hcond _ (List.mem_append_left _ (hmem_merge _))

/-- Dual of `hintikkaS4_box_pos_self` for the diamond-negative shape: `F(◇ψ)@w ∈ b` implies
`F(ψ)@w ∈ b` (same world, via `modalTDiaNegSelf`). Exact mirror of
`hintikkaS4_box_pos_self`'s proof. -/
lemma hintikkaS4_dia_neg_self
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.neg, .diamond ψ, w⟩ hmem
  simp only at hcond
  have hshape : modalApplyOneS4 φ₀ ⟨.neg, .diamond ψ, w⟩ b acc =
      modalApplyOneS4Rules ⟨.neg, .diamond ψ, w⟩ b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  by_cases hinb :
      (b.any fun x => x == (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
  · simp only [List.any_eq_true, beq_iff_eq] at hinb
    obtain ⟨sf', hsf'mem, rfl⟩ := hinb
    exact hsf'mem
  · have htarget_mem_self :
        (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalTDiaNegSelf b ψ w := by
      unfold modalTDiaNegSelf
      simp [hinb]
    have htR :
        (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        (match (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTDiaNegSelf b ψ w)
          | other => other) := by
      unfold modalApplyOneT
      obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc
      cases kResult <;> first | rfl | (simp only []; split <;> rfl)
    have hk :
        (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
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
    rw [hk] at htR
    rw [htR] at hcond
    have hselfNotEmpty : ¬ (modalTDiaNegSelf b ψ w).isEmpty = true := by
      have hne : (modalTDiaNegSelf b ψ w).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, htarget_mem_self⟩
      simp [hne]
    simp only [if_neg hselfNotEmpty] at hcond
    have hmem_merge : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex)),
        (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          l ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(l.any (· == x))) := by
      intro l
      by_cases hinl :
          (l.any fun x => x == (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
            = true
      · simp only [List.any_eq_true, beq_iff_eq] at hinl
        obtain ⟨sf', hsf'mem, rfl⟩ := hinl
        exact List.mem_append_left _ hsf'mem
      · refine List.mem_append_right _ ?_
        simp only [List.mem_filter]
        exact ⟨htarget_mem_self, by simp [hinl]⟩
    split_ifs at hcond with h1 <;> simp only at hcond
    · exact hcond _ (List.mem_append_left _ htarget_mem_self)
    · exact hcond _ (List.mem_append_left _ htarget_mem_self)
    · exact hcond _ (List.mem_append_left _ (hmem_merge _))
    · exact hcond _ (List.mem_append_left _ (hmem_merge _))

/-- Box-negative witness bridge for S4: `F(□ψ)@w ∈ b` implies `∃ w', acc.hasEdge w w' = true
∧ F(ψ)@w' ∈ b` -- a one-line projection off `modalHintikkaSetS4`'s third conjunct (Decision
D3: this conjunct is apply-agnostic and copied unchanged from `modalHintikkaSet`). Mirrors
`hintikka_box_neg` (`Completeness.lean`). -/
lemma hintikkaS4_box_neg
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2.1 ψ w hmem

/-- Diamond-positive witness bridge for S4: `T(◇ψ)@w ∈ b` implies `∃ w', acc.hasEdge w w' =
true ∧ T(ψ)@w' ∈ b` -- a one-line projection off `modalHintikkaSetS4`'s fourth conjunct.
Mirrors `hintikka_diamond_pos` (`Completeness.lean`). -/
lemma hintikkaS4_diamond_pos
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2.2 ψ w hmem

/-! ## The `ReflTransGen` Path Bridge (the Crux) -/

/-- **The crux of the task**: `modalHintikkaSetS4 φ₀ b acc`, `T(□ψ)@w ∈ b`, and a
`Relation.ReflTransGen`-path `w ⤳ w'` in `acc.hasEdge` together imply `T(ψ)@w' ∈ b`. Proved
by `Relation.ReflTransGen.head_induction_on`, carrying `T(□ψ)@·` along each edge via
`hintikkaS4_box_pos_step` and discharging the endpoint (including the reflexive `w = w'`
base case) via `hintikkaS4_box_pos_self`. This is exactly why the 4-rule propagates the box
*itself* rather than its unwrapped body: the induction's invariant needs `T(□ψ)` to survive
every intermediate edge, not just the final one, and only `T(□ψ)@·`, not `T(ψ)@·`, is
preserved by a single `hasEdge` step in general.

Loop-back cycles in `acc` are harmless here: `Relation.ReflTransGen` is the reflexive-
transitive *closure*, so revisiting a world via a cycle contributes no new reachable worlds
beyond those already related by the path; the induction recurses on the *path witness*
(`hpath`'s structure), not on the graph, so it terminates regardless of cycles in `acc`. -/
lemma hintikkaS4_box_pos_reflTransGen
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hpath : Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  revert hmem
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => intro hmem; exact hintikkaS4_box_pos_self φ₀ b acc hH ψ w' hmem
  | head hedge _ ih =>
    intro hmem
    exact ih (hintikkaS4_box_pos_step φ₀ b acc hH ψ _ _ hmem hedge)

/-- Dual of `hintikkaS4_box_pos_reflTransGen` for the diamond-negative shape: `F(◇ψ)@w ∈ b`
and a `ReflTransGen`-path `w ⤳ w'` in `acc.hasEdge` together imply `F(ψ)@w' ∈ b`. -/
lemma hintikkaS4_dia_neg_reflTransGen
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hpath : Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  revert hmem
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => intro hmem; exact hintikkaS4_dia_neg_self φ₀ b acc hH ψ w' hmem
  | head hedge _ ih =>
    intro hmem
    exact ih (hintikkaS4_dia_neg_step φ₀ b acc hH ψ _ _ hmem hedge)

/-! ## Sanity Checks

`modalTableauS4` was confirmed to evaluate and close exactly on the T and 4 components via
an interactive `#eval` session (not embedded in this file as a permanent `#eval`/`#guard`/
`native_decide` declaration: this file's `module`/`public meta import` boundary makes all
three of those forms either fail to elaborate (`Proposition.atom` is not `meta`-accessible
without an additional `public meta import`) or fail at the native-code-lookup stage
(`modalFuel`'s compiled implementation is not resolvable in this configuration) -- no
existing file in `Cslib/Logics/Modal/Tableau/` uses any of these forms, confirming this is a
structural constraint of the module system here, not specific to this phase's code).
Confirmed interactively:
- `□p → p` (the T schema) evaluates to `.closed`: S4 is reflexive.
- `□p → □□p` (the 4 schema) evaluates to `.closed`: S4 is transitive -- this is the
  component that distinguishes S4 from T, and the entire reason this task's 4-rule exists.
- A bare atom `p` evaluates to `.openBranch _ _`: S4 does not prove arbitrary atoms. -/

/-! ## The S4 Loop Invariant `S4LoopInv` -/

/-- **Correction 1**: `S4LoopInv` is a **sibling** of `ModalPotentialInv` (`FmpMeasure.lean`),
not an extension of it. `ModalPotentialInv` holds two rank fields (`rankBound`/`rankEdge`)
encoding "modal depth strictly decreases along every edge", which the 4-rule (placing
`T(□ψ)`, unchanged modal depth, at a successor) and loop-back edges (creating `w → w''`
with `rank w'' + 2 = rank w`) both falsify. `S4LoopInv` reuses the six rule-independent
fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`, over
`modalUniverseS4` in place of `modalUniverse`), omits the two rank fields entirely, and adds
the four **stable birth-key** fields (task 511 Phase 4, replacing the structurally-unsound
`worldSetsDistinct`): `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse`, stated over
the threaded `keys` list (`modalStepBranchS4Keyed`) rather than the live branch. `keys` never
changes after a world is born and each key only ever lower-bounds a monotonically-growing live
relevant set, so this invariant survives every step (Gap 1), and `keysDistinct` is exactly
what the birth-content guard `blockingWorldS4` enforces at minting time (Gap 2).
`FmpMeasure.lean` is not modified by this plan. -/
structure S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop where
  /-- Every branch formula is a member of the fixed finite S4 universe `U_{S4}(φ₀)`. -/
  bClosure : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀
  /-- The expanded set has no duplicate entries. -/
  eNodup : e.Nodup
  /-- Every expanded-set formula is a member of `U_{S4}(φ₀)`. -/
  eClosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀
  /-- All of `acc`'s recorded worlds are `< modalNextWorld b`. -/
  accFresh : accFreshInv b acc
  /-- Every `acc`-edge target is a label already appearing on the branch. -/
  accKnown : accTargetsKnown b acc
  /-- `outDeg` exactly counts the minting-shaped formulas in `e` at each world. -/
  outDegEq : ∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length
  /-- Every known world has a recorded birth key. -/
  keysTotal : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys
  /-- **Survives Gap 1**: a world's recorded birth key is a LOWER BOUND on its live relevant
  set. This is monotone-stable -- birth keys never change after a world is born, and live
  relevant sets only grow (`relevantSetFinset_mono`) -- unlike the old `worldSetsDistinct`,
  which compared live sets directly and so could be falsified by a later persistent step. -/
  keyLowerBd : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w
  /-- **Fixes Gap 2**: distinct worlds have DISTINCT birth keys. This is exactly what the
  redesigned guard (`blockingWorldS4`) enforces at minting time (`blockingWorldS4_none_fresh`),
  and no later step can violate it since keys themselves never change. This is the hypothesis
  the pigeonhole argument (`modalKnownWorlds_length_le_worldBoundS4`, Phase 6) consumes. -/
  keysDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k'
  /-- Birth keys are drawn from the powerset of the finite signed-subformula codomain
  `signedSubfmls φ₀`: the pigeonhole argument's injection target (Phase 6). -/
  keysInUniverse : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀

/-! ## `bClosure`/`eClosure` (task 511, Phase 5 -- documented strategic-sorry skeletons)

Both remaining `S4LoopInv` fields need machinery genuinely beyond a mechanical case split:

- **`eClosure`** needs a formula-subset composite for the T-self (`modalTBoxSelf`/
  `modalTDiaNegSelf`, `FrameRules.lean`) and 4-propagation (`modalFourBoxProp`/
  `modalFourDiaNegProp`) outputs at the 12 non-minting shapes' T/4-relevant leaves, mirroring
  `modalApplyOneT_boxPos_diaNeg_known_S4`/`modalApplyOneS4Rules_boxPos_diaNeg_known_S4`'s
  existing case-split shape but concluding `x.formula ∈ modalSubfmls sf.formula` (via K's own
  PUBLIC `modalApplyOne_boxPos_outputs_subset`/`modalApplyOne_diamondNeg_outputs_subset` for the
  underlying K piece, plus trivial `modalSubfmls_self_mem`-style facts for the T-self/4-prop
  pieces, since T-self emits the box/diamond's own argument -- one step into `modalSubfmls
  sf.formula` -- and 4-prop emits `sf.formula` itself unchanged) then composing via
  `modalSubfmls_trans_S4` with `hb`'s own bound on `sf`. At the 2 minting shapes, the new
  formulas' bound is already available via the `keyLowerBd`-adjacent groundwork
  (`successorBirthContent_boxNeg_subset_relevantSetFinset`-style reasoning extended to
  `modalUniverseS4` membership rather than `relevantSetFinset`).
- **`bClosure`** needs the label-side bound `modalMaxWorld b < modalWorldBoundS4 φ₀` (the STRICT
  form) available BEFORE any mint can occur, so the newly-minted witness's label
  (`modalNextWorld b = modalMaxWorld b + 1`) stays `≤ modalWorldBoundS4 φ₀`. This is exactly
  Phase 6's own pigeonhole deliverable (`modalKnownWorlds_nodup` +
  `modalKnownWorlds_length_le_worldBoundS4`, injecting known worlds into `keys` via `keysTotal`/
  `keysDistinct`/`keysInUniverse`, cardinality via `signedSubfmls_powerset_card` +
  `List.Nodup.length_le_card`/`Finset.card_le_card_of_injOn`, then a "worlds are consecutive from
  0" fact to convert the length bound into a STRICT `modalMaxWorld` bound) -- genuinely a
  prerequisite of `bClosure`'s OWN preservation, not merely Phase 6's later corollary, since
  `bClosure`'s minting-case obligation needs the bound to hold on the PRE-step branch `b` to
  guarantee the freshly-minted label stays in range. Both are landed here as complete theorem
  STATEMENTS (not vacuous placeholders) with `sorry` bodies, each carrying every hypothesis its
  own preservation genuinely needs (mirroring every other field's signature shape in this
  section) -- ready for a continuation dispatch to discharge without any further design work. -/

/-- **`eClosure`'s driver-level preservation -- STRATEGIC SORRY** (task 511, Phase 5, documented
gap; see the section docstring above for the exact remaining proof obligation). -/
lemma modalStepBranchS4_preserves_eClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀)
    (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverseS4 φ₀ := by
  sorry

/-- **`bClosure`'s driver-level preservation -- STRATEGIC SORRY** (task 511, Phase 5, documented
gap; see the section docstring above for the exact remaining proof obligation -- the pigeonhole
world-bound argument, Phase 6's own core deliverable, is a genuine prerequisite here). -/
lemma modalStepBranchS4_preserves_bClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverseS4 φ₀ := by
  sorry

/-- **`modalStepBranchS4_preserves_S4LoopInv`** (task 511, Phase 5 assembly): every
`modalStepBranchS4Keyed` step preserves `S4LoopInv`, over every branch/expanded-set pair it
produces (any `b' ∈ newBs` paired with any `e' ∈ newExps` -- valid because `modalStepBranchS4Keyed`
never produces distinct `newExps` entries for distinct `newBs` entries: the `.branching` arm
maps EVERY branch to the identical `e ++ [sf]`, and the `.linear`/`.persistent` arms produce
singleton lists of each, so any member of one is definitionally paired with any member of the
other). Also threads and re-establishes the proof-internal `keysWorldsKnown` auxiliary invariant
(not an `S4LoopInv` field itself, `modalStepBranchS4_preserves_keysWorldsKnown`'s own
docstring) needed by `accFresh`/`accKnown`'s own preservation, so a continuation dispatch driving
this assembly through repeated steps (Phase 6/7) can re-supply it at each call.

**Eight of the ten fields are fully closed, zero sorry** (`keysDistinct`/`keyLowerBd`/
`keysInUniverse`/`keysTotal`: the four "key" fields, closed across dispatches 2-5; `eNodup`/
`outDegEq`/`accFresh`/`accKnown`: closed this dispatch). **Two fields
(`bClosure`/`eClosure`) are documented strategic-sorry skeletons** -- see the section docstring
immediately above `modalStepBranchS4_preserves_eClosure` for the precise remaining obligation
each needs; both are genuinely non-mechanical (the `bClosure` gap in particular requires Phase
6's own pigeonhole deliverable as a prerequisite, not merely a corollary). -/
theorem modalStepBranchS4_preserves_S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4LoopInv φ₀ b e acc keys)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    (∀ b' ∈ newBs, ∀ e' ∈ newExps, S4LoopInv φ₀ b' e' newAcc keys') ∧
    (∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b') := by
  obtain ⟨hbC, heN, heC, haF, haK, hoD, hkT, hkL, hkD, hkI⟩ := hinv
  refine ⟨?_, modalStepBranchS4_preserves_keysWorldsKnown φ₀ b e acc keys newBs newExps newAcc
    keys' hKW hstep⟩
  intro b' hb' e' he'
  exact
    { bClosure := modalStepBranchS4_preserves_bClosure φ₀ b e acc keys newBs newExps newAcc keys'
        hbC hkT hkD hkI haK hstep b' hb'
      eNodup := modalStepBranchS4_preserves_eNodup φ₀ b e acc keys newBs newExps newAcc keys'
        hstep heN e' he'
      eClosure := modalStepBranchS4_preserves_eClosure φ₀ b e acc keys newBs newExps newAcc keys'
        hbC heC haK hstep e' he'
      accFresh := modalStepBranchS4_preserves_accFresh φ₀ b e acc keys newBs newExps newAcc keys'
        haK hKW haF hstep b' hb'
      accKnown := modalStepBranchS4_preserves_accKnown φ₀ b e acc keys newBs newExps newAcc keys'
        haK hKW hstep b' hb'
      outDegEq := modalStepBranchS4_preserves_outDegEq φ₀ b e acc keys newBs newExps newAcc keys'
        haK hoD hstep e' he'
      keysTotal := modalStepBranchS4_preserves_keysTotal φ₀ b e acc keys newBs newExps newAcc
        keys' haK hkT hstep b' hb'
      keyLowerBd := modalStepBranchS4_preserves_keyLowerBd φ₀ b e acc keys newBs newExps newAcc
        keys' hbC hkL hstep b' hb'
      keysDistinct := modalStepBranchS4_preserves_keysDistinct φ₀ b e acc keys newBs newExps
        newAcc keys' hkD hstep
      keysInUniverse := modalStepBranchS4_preserves_keysInUniverse φ₀ b e acc keys newBs newExps
        newAcc keys' hbC hkI hstep }

end Cslib.Logic.Modal.Tableau

end
