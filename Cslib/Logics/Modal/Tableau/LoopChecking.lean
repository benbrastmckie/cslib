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

end Cslib.Logic.Modal.Tableau

end
