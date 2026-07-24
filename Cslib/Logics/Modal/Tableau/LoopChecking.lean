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

**Redesign note**: an earlier `blockingWorld` guard and `worldSetsDistinct` invariant were
both found to be structurally unsound -- distinctness
over the *live* branch is not a loop invariant (relevant sets grow monotonically), and the
guard compared the *source* world's set rather than the *prospective successor's* birth
content. This module now uses `blockingWorldS4`/`successorBirthContent` (stable birth-content
guard) and `S4LoopInv`'s `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse` fields
(stable per-world birth keys) in their place.

## Main Definitions

- `formulasAtWorld`: the sub-list of a branch's signed formulas at a given world.
- `sameRelevantSet`: the decidable equality-of-relevant-formula-set test over
  `modalSubfmls φ₀`, used for comparison (retained as the comparison primitive).
- `signedSubfmls`/`relevantSetFinset`: the finite `Finset (Sign × Proposition Atom)` codomain
  and the live relevant set restated as a `Finset`.
- `successorBirthContent`/`blockingWorldS4`: the redesigned minting guard:
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
can create (below), since each world's *birth key* is a distinct element of the powerset of
`modalSubfmls φ₀ × Sign` -- the *birth key*, not the live relevant set, is what the
pigeonhole argument now injects (see `S4LoopInv`).

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
the pigeonhole argument below consumes: `worldSetsDistinct` demands that every pair of
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
cardinality of `powerset (Sign × modalSubfmls φ₀)` (the
`sameRelevantSet`/birth-key notion distinguishes *both signs*, so the pigeonhole codomain is
`powerset(Sign × Sf)`, not `powerset(Sf)`; `2^|Sf|` is unprovably small). `modalWork`/
`modalExpMeasure` (`FmpMeasure.lean`) are reused **verbatim**: they take the universe `U` as
an explicit parameter and are rule/world-agnostic. `geomCap`/`modalPotential`/
`modalPotentialTerm` do **not** transfer -- they are the geometric tree-capacity argument
specific to `modalWorldBound`. -/

/-- The S4 world bound: `2 ^ (2 * |modalSubfmls φ₀|)`, the number of possible
signed-relevant-formula sets, i.e. `(signedSubfmls φ₀).powerset.card` (Decision D2). Replaces
`modalWorldBound`'s branching^depth tree bound,
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

/-- The S4-specific closed-form fuel bound for the keyed driver, built the same way `modalFuel`
is (`Saturation.lean`) but over the S4 pigeonhole world bound `modalWorldBoundS4` instead of the
tree-shaped `modalWorldBound`: `modalFuel φ₀` is confirmed NOT provably sufficient for the S4
keyed loop (at `modalComplexity φ₀ = 0`, `modalWorldBoundS4 φ₀ = 4` exceeds K's
`modalWorldBound φ₀ = 1`). Declared here (alongside `modalWorldBoundS4`/`modalUniverseS4`) so it
is in scope for `modalTableauS4Keyed`'s fuel argument below; sufficiency is proved later by
`modalExpMeasure_entry_le_fuelS4`. -/
def modalFuelS4 (φ₀ : Proposition Atom) : Nat :=
  3 ^ (4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1))

/-! ## Signed-Key Finite Codomain

The stable-key infrastructure the redesigned guard/invariant below consumes: the fixed
finite codomain `signedSubfmls φ₀` (both signs × every subformula of `φ₀`, as a `Finset`) and
the live relevant set `relevantSetFinset φ₀ b w` restated as a `Finset` (reusing
`sameRelevantSet`'s membership notion). No driver change here -- pure defs + lemmas,
CI-green in isolation. -/

/-- The finite signed-subformula codomain: both signs paired with every subformula of `φ₀`, as
a `Finset (Sign × Proposition Atom)`. This is the fixed codomain the pigeonhole argument
(`modalKnownWorlds_length_le_worldBoundS4`, below) injects known worlds into, via their birth
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
cardinality bridge the pigeonhole argument below consumes (`Finset.card_powerset` plus
`signedSubfmls_card_le`, monotone in the exponent). This is why the exponent fix above
precedes: it ties the bound to `2 ^ (2·|Sf|)`, the correct codomain size for a sign-distinguishing
key. -/
lemma signedSubfmls_powerset_card_le (φ₀ : Proposition Atom) :
    (signedSubfmls φ₀).powerset.card ≤ modalWorldBoundS4 φ₀ := by
  unfold modalWorldBoundS4
  rw [Finset.card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) (signedSubfmls_card_le φ₀)

/-- The live relevant set `R(b,w)` as a `Finset`: exactly the
elements of `signedSubfmls φ₀` whose signed-formula instantiation at `w` is present on `b`.
Reuses `sameRelevantSet`'s membership notion (`⟨s,ψ,w⟩ ∈ b`) restated as a finite set for the
birth-key / pigeonhole machinery below. -/
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
the fact Gap 1 exploited for the old live-branch invariant, and the
fact the new lower-bound invariant (`S4LoopInv.keyLowerBd`, below) is designed to *survive*:
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

/-! ## Minting Guard (redesigned to fix Gap 2)

**Gap 2**: the *original* `blockingWorld` guard compared the *source*
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
exactly the property that makes `S4LoopInv.keyLowerBd` (below) a genuine loop invariant
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
`modalApplyOne` (raw K) at an unblocked minting shape -- same underlying rule as
`modalApplyOneS4`'s own unblocked reduction (`modalApplyOneS4_boxNeg_unblocked_eq`/dual), just
gated by a different guard. `modalApplyOneS4`/`blockingWorldS4` are NOT modified or removed:
they remain the live-set-guarded artifact the Hintikka/truth-lemma bridges consume. -/
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
`modalUniverse_mem_label`. -/
private lemma modalUniverseS4_mem_label {φ₀ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverseS4 φ₀) :
    x.label ≤ modalWorldBoundS4 φ₀ := by
  simp only [modalUniverseS4, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, ψ, -, heq | heq⟩ := hx <;> (subst heq; exact Nat.lt_succ_iff.mp hw)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Constructor direction for `modalUniverseS4` membership: a signed formula with any sign,
a subformula of `φ₀`, at a world label within the bound, is in `U_{S4}(φ₀)`. S4-local
restatement of `FmpMeasure.lean`'s file-private `mem_modalUniverse_of`. -/
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

/-! ## Minting-Content Universe-Membership (groundwork for `bClosure`)

S4-local restatements of `FmpMeasure.lean`'s file-private subformula-closure facts for the
world-preserving and fresh-world minting rules
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

/-! ## Minting-Content Equality Closure

This section closes `keyLowerBd`'s minting-case obligation using the groundwork above:
`successorBirthContent φ₀ b s φ w ⊆ relevantSetFinset φ₀ (newForms ++ b)
(modalNextWorld b)`. `keyLowerBd` itself only demands `⊆` (not `=`), so only the forward
direction is proved -- narrower than an earlier `Finset.ext` attempt, which chased
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

/-! ## Assembling `keyLowerBd`'s Preservation -/

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

/-- **`keyLowerBd`'s driver-level preservation**: every key
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

/-- **`keysInUniverse`'s driver-level preservation**: every key
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

/-! ## Assembling `keysTotal`'s Preservation -/

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

/-- **`keysTotal`'s driver-level preservation** (the crux): every
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

/-- **`keysDistinct`'s driver-level preservation**: every pair of
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
one would reopen the already-finalized struct design): every RECORDED key's world is
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

/-! ## Pigeonhole World Bound -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Generalized max-fold bound: if every element's label in `l` is `≤ K` and the starting
accumulator `a` is also `≤ K`, the fold never exceeds `K`. Groundwork for
`modalMaxWorld_le_of_forall_label_le`. -/
private lemma foldl_max_le_of_forall_le
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (K a : WorldIndex)
    (ha : a ≤ K) (h : ∀ sf ∈ l, sf.label ≤ K) :
    l.foldl (fun mx sf => max mx sf.label) a ≤ K := by
  induction l generalizing a with
  | nil => simpa
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (max a hd.label) (Nat.max_le.mpr ⟨ha, h hd List.mem_cons_self⟩)
      (fun sf hsf => h sf (List.mem_cons_of_mem _ hsf))

omit [DecidableEq Atom] [Hashable Atom] in
/-- If every element of `l` has label `≤ K`, then `modalMaxWorld l ≤ K`. Needed to bound the
post-step branch's `modalMaxWorld` without needing to unfold the mint content's literal shape at
every call site. -/
private lemma modalMaxWorld_le_of_forall_label_le
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (K : WorldIndex)
    (h : ∀ sf ∈ l, sf.label ≤ K) : modalMaxWorld l ≤ K := by
  unfold modalMaxWorld
  exact foldl_max_le_of_forall_le l K 0 (Nat.zero_le _) h

/-- **Proof-internal auxiliary invariant**: the known worlds of a branch
form the contiguous range `{0, ..., modalMaxWorld b}` -- not an `S4LoopInv` field (would reopen
the finalized struct design), threaded as an extra hypothesis/conclusion alongside the
struct at every call site, exactly like `keysWorldsKnown`. Holds by construction: the driver
only ever mints the SINGLE next integer `modalNextWorld b = modalMaxWorld b + 1`, never skipping
a label -- this is the "worlds are consecutive from 0" fact `modalStepBranchS4_worldBound`
converts a pigeonhole *length* bound into a STRICT `modalMaxWorld` bound with. -/
def worldsContiguousS4 (b : List (SignedFormula (Proposition Atom) WorldIndex)) : Prop :=
  ∀ w, w ≤ modalMaxWorld b → w ∈ modalKnownWorlds b

/-- `worldsContiguousS4`'s driver-level preservation: mirrors `keysWorldsKnown`'s assembly shape
(top split on minting vs. non-minting, reusing `modalStepBranchS4Keyed_branch_superset` for the
"old worlds carry over" half). At the 12 non-minting shapes, every emitted formula's label is
already a known world of `b` (`modalApplyOneS4Keyed_nonMint_known_S4`), so `modalMaxWorld`
cannot grow. At the 2 minting UNBLOCKED shapes, every emitted formula's label is exactly
`modalNextWorld b` (`mintGroup_label_eq_freshWorld_S4`), so `modalMaxWorld` grows by exactly the
one new label, which is directly known via the witness formula's own membership. At the BLOCKED
sub-case, `result = .linear []` so the branch is unchanged. -/
lemma modalStepBranchS4_preserves_worldsContiguousS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hWC : worldsContiguousS4 b) (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, worldsContiguousS4 b' := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w ≤ modalMaxWorld b, w ∈ modalKnownWorlds b' := by
    intro b' hb' w hw
    obtain ⟨sf', hsf'mem, hlab⟩ := (mem_modalKnownWorlds_S4 b w).mp (hWC w hw)
    exact (mem_modalKnownWorlds_S4 b' w).mpr ⟨sf', hsuper b' hb' sf' hsf'mem, hlab⟩
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
        have hresulteq : result = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans (modalApplyOne_boxNeg_mint_fst_S4 b acc ψ sf.label)
        have hlabel := mintGroup_label_eq_freshWorld_S4 b sf.label .neg ψ
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rw [hlabel sf'' hnew]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds_S4]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩, List.mem_append_left _ List.mem_cons_self, rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
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
        have hresulteq2 := hresulteq.trans (modalApplyOne_diamondPos_mint_fst_S4 b acc ψ sf.label)
        have hlabel := mintGroup_label_eq_freshWorld_S4 b sf.label .pos ψ
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rw [hlabel sf'' hnew]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds_S4]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩, List.mem_append_left _ List.mem_cons_self, rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb'
    have hmaxle : modalMaxWorld b' ≤ modalMaxWorld b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds_S4 b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ := (mem_modalKnownWorlds_S4 b sf''.label).mp
            (hnm sf'' (List.mem_flatten.mpr ⟨br, hbr, hnew⟩))
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds_S4 b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf; simp at hsf
    intro w hw
    exact hold b' hb' w (le_trans hw hmaxle)

omit [DecidableEq Atom] [Hashable Atom] in
/-- `modalKnownWorlds`'s dedup-guarded `foldl` never produces duplicates. Local re-derivation of
`FmpMeasure.lean`'s file-private `modalKnownWorlds_nodup` (unavailable across files). -/
lemma modalKnownWorlds_nodup_S4
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) : (modalKnownWorlds l).Nodup := by
  have key : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex))
      (ws0 : List WorldIndex), ws0.Nodup →
      (l.foldl (fun ws sf => if ws.any (· == sf.label) then ws else sf.label :: ws) ws0).Nodup := by
    intro l
    induction l with
    | nil => intro ws0 hws0; simpa
    | cons sf rest ih =>
      intro ws0 hws0
      by_cases hc : ws0.any (· == sf.label)
      · simp only [List.foldl_cons, if_pos hc]
        exact ih ws0 hws0
      · simp only [List.foldl_cons, if_neg hc]
        have hnotmem : sf.label ∉ ws0 := by simpa [List.any_eq_true] using hc
        exact ih (sf.label :: ws0) (List.nodup_cons.mpr ⟨hnotmem, hws0⟩)
  unfold modalKnownWorlds
  exact key l [] List.nodup_nil

omit [Hashable Atom] in
/-- **The pigeonhole cardinality bound**: the number of known worlds of a branch is
bounded by `modalWorldBoundS4 φ₀`. Injects known worlds into `keys` via `keysTotal`, injectivity
via `keysDistinct`, codomain bound via `keysInUniverse` + `signedSubfmls_powerset_card_le`,
cardinality via `Finset.card_le_card_of_injOn`. -/
lemma modalKnownWorlds_length_le_worldBoundS4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    (modalKnownWorlds b).length ≤ modalWorldBoundS4 φ₀ := by
  classical
  set f : WorldIndex → Finset (Sign × Proposition Atom) :=
    fun w => if hw : w ∈ modalKnownWorlds b then (hKT w hw).choose else ∅ with hf
  have hmapsto : ∀ w ∈ (modalKnownWorlds b).toFinset, f w ∈ (signedSubfmls φ₀).powerset := by
    intro w hw
    rw [List.mem_toFinset] at hw
    simp only [hf, dif_pos hw]
    rw [Finset.mem_powerset]
    exact hKI w _ (hKT w hw).choose_spec
  have hinj : Set.InjOn f (modalKnownWorlds b).toFinset := by
    intro w1 hw1 w2 hw2 heq
    simp only [Finset.mem_coe, List.mem_toFinset] at hw1 hw2
    by_contra hne
    have hk1 : (w1, f w1) ∈ keys := by
      simp only [hf, dif_pos hw1]; exact (hKT w1 hw1).choose_spec
    have hk2 : (w2, f w2) ∈ keys := by
      simp only [hf, dif_pos hw2]; exact (hKT w2 hw2).choose_spec
    exact (hKD w1 w2 (f w1) (f w2) hk1 hk2 hne) heq
  have hcard := Finset.card_le_card_of_injOn f hmapsto hinj
  rw [List.toFinset_card_of_nodup (modalKnownWorlds_nodup_S4 b)] at hcard
  calc (modalKnownWorlds b).length ≤ (signedSubfmls φ₀).powerset.card := hcard
    _ ≤ modalWorldBoundS4 φ₀ := signedSubfmls_powerset_card_le φ₀

omit [Hashable Atom] in
/-- **`modalStepBranchS4_worldBound`**: the
STRICT world bound `modalMaxWorld b < modalWorldBoundS4 φ₀`, the deliverable that makes any
fresh mint's label (`modalNextWorld b = modalMaxWorld b + 1`) stay within `modalWorldBoundS4`'s
fixed range. Combines the pigeonhole length bound
(`modalKnownWorlds_length_le_worldBoundS4`) with the density fact `worldsContiguousS4` provides:
`{0, ..., modalMaxWorld b} ⊆ modalKnownWorlds b`, so `modalMaxWorld b + 1 ≤
(modalKnownWorlds b).length ≤ modalWorldBoundS4 φ₀`. -/
lemma modalStepBranchS4_worldBound (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    modalMaxWorld b < modalWorldBoundS4 φ₀ := by
  have hlen := modalKnownWorlds_length_le_worldBoundS4 φ₀ b keys hKT hKD hKI
  have hsub : (List.range (modalMaxWorld b + 1)).toFinset ⊆ (modalKnownWorlds b).toFinset := by
    intro w hw
    rw [List.mem_toFinset, List.mem_range] at hw
    rw [List.mem_toFinset]
    exact hWC w (Nat.lt_succ_iff.mp hw)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup List.nodup_range,
      List.toFinset_card_of_nodup (modalKnownWorlds_nodup_S4 b), List.length_range] at hcard
  calc modalMaxWorld b < modalMaxWorld b + 1 := Nat.lt_succ_self _
    _ ≤ (modalKnownWorlds b).length := hcard
    _ ≤ modalWorldBoundS4 φ₀ := hlen

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
proved from the driver here) -- `modalExpandBranchesS4_hintikka` (below) is
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

/-- **Bridge**: `modalHintikkaSetS4 φ₀` is exactly `modalHintikkaSetGen
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
the four **stable birth-key** fields (replacing the structurally-unsound
`worldSetsDistinct`): `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse`, stated over
the threaded `keys` list (`modalStepBranchS4Keyed`) rather than the live branch. `keys` never
changes after a world is born and each key only ever lower-bounds a monotonically-growing live
relevant set, so this invariant survives every step (Gap 1), and `keysDistinct` is exactly
what the birth-content guard `blockingWorldS4` enforces at minting time (Gap 2).
`FmpMeasure.lean` is not modified here. -/
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
  the pigeonhole argument (`modalKnownWorlds_length_le_worldBoundS4`, below) consumes. -/
  keysDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k'
  /-- Birth keys are drawn from the powerset of the finite signed-subformula codomain
  `signedSubfmls φ₀`: the pigeonhole argument's injection target (below). -/
  keysInUniverse : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀

/-! ## `bClosure`/`eClosure` (both fully closed)

Both remaining `S4LoopInv` fields, closed:

- **`eClosure`** turned out to be immediate: `modalStepBranchS4Keyed`'s `newExps` component is
  `e ++ [sf]` (or `e` unchanged for `.persistent`) -- it only ever gains the *selected* formula
  `sf` (already `∈ b`, hence covered directly by `hb`), never the rule's output content (that
  goes to `newBs`, `bClosure`'s concern).
- **`bClosure`** needed exactly that formula-subset composite (`modalApplyOneS4Keyed_nonMint_
  universe_S4` and its supporting T-augmented/S4Rules-augmented pieces, "Non-Minting
  Universe-Membership Composite" section above) for its 12 non-minting shapes, plus the
  pigeonhole world-bound deliverable (`modalStepBranchS4_worldBound`, "Pigeonhole World
  Bound" section above) as a genuine PREREQUISITE for its 2 minting shapes: the newly-minted
  witness's label (`modalNextWorld b = modalMaxWorld b + 1`) needs the STRICT bound
  `modalMaxWorld b < modalWorldBoundS4 φ₀` to hold on the PRE-step branch `b`, which is exactly
  what `modalStepBranchS4_worldBound` supplies (consuming a new proof-internal auxiliary
  invariant `worldsContiguousS4`, threaded the same way as `keysWorldsKnown`). -/

/-- **`eClosure`'s driver-level preservation**: closes directly via the same case-split shape as
`modalStepBranchS4_preserves_eNodup` -- `newExps`'s only new content is the selected formula
`sf`, already in `b` and hence covered by `hb`. -/
lemma modalStepBranchS4_preserves_eClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀)
    (_hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverseS4 φ₀ := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfbound : sf ∈ modalUniverseS4 φ₀ := hb sf hsfmem
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
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x0, -, rfl⟩ := List.mem_map.mp he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact heclosure
  · rw [hres] at hsf; simp at hsf

/-- **`bClosure`'s driver-level preservation**: at the 12 non-minting shapes, the "Non-Minting
Universe-Membership Composite" section's `modalApplyOneS4Keyed_nonMint_universe_S4` bounds
emitted content directly; at the 2 minting shapes, the pigeonhole world-bound
(`modalStepBranchS4_worldBound`, consuming `worldsContiguousS4`) supplies the STRICT
`modalMaxWorld b < modalWorldBoundS4 φ₀` bound `modalApplyOne_boxNeg_outputs_subset_S4`/
`modalApplyOne_diamondPos_outputs_subset_S4` need to place the freshly-minted witness in
range. -/
lemma modalStepBranchS4_preserves_bClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverseS4 φ₀ := by
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
        have hresulteq : result = (modalApplyOne (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans (modalApplyOne_boxNeg_mint_fst_S4 b acc ψ sf.label)
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_boxNeg_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
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
        have hresulteq2 := hresulteq.trans (modalApplyOne_diamondPos_mint_fst_S4 b acc ψ sf.label)
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_diamondPos_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem'
          hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_universe_S4 φ₀ keys sf b acc hb hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' x hx
    rcases hres : result with lf | brs | lf | -
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x (List.mem_flatten.mpr ⟨br, hbr, hxnew⟩)
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf; simp at hsf

/-- **`modalStepBranchS4_preserves_S4LoopInv`**: every `modalStepBranchS4Keyed` step preserves
`S4LoopInv`, over every
branch/expanded-set pair it produces (any `b' ∈ newBs` paired with any `e' ∈ newExps` -- valid
because `modalStepBranchS4Keyed` never produces distinct `newExps` entries for distinct `newBs`
entries: the `.branching` arm maps EVERY branch to the identical `e ++ [sf]`, and the
`.linear`/`.persistent` arms produce singleton lists of each, so any member of one is
definitionally paired with any member of the other). Also threads and re-establishes TWO
proof-internal auxiliary invariants (neither an `S4LoopInv` field itself, to avoid reopening the
finalized struct design): `keysWorldsKnown` (needed by `accFresh`/`accKnown`) and
`worldsContiguousS4` (needed by `bClosure`'s own minting-case pigeonhole prerequisite,
`modalStepBranchS4_worldBound`), so repeated steps through this assembly can re-supply both at
each call.

**All ten fields are now fully closed, zero sorry** (`keysDistinct`/`keyLowerBd`/
`keysInUniverse`/`keysTotal`: the four "key" fields; `eNodup`/
`outDegEq`/`accFresh`/`accKnown`; and `eClosure`/`bClosure`,
`eClosure` directly and `bClosure` via the pigeonhole world-bound
(`modalStepBranchS4_worldBound`) as a genuine prerequisite for its minting-case obligation). -/
theorem modalStepBranchS4_preserves_S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4LoopInv φ₀ b e acc keys)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hWC : worldsContiguousS4 b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    (∀ b' ∈ newBs, ∀ e' ∈ newExps, S4LoopInv φ₀ b' e' newAcc keys') ∧
    (∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b') ∧
    (∀ b' ∈ newBs, worldsContiguousS4 b') := by
  obtain ⟨hbC, heN, heC, haF, haK, hoD, hkT, hkL, hkD, hkI⟩ := hinv
  refine ⟨?_, modalStepBranchS4_preserves_keysWorldsKnown φ₀ b e acc keys newBs newExps newAcc
    keys' hKW hstep, modalStepBranchS4_preserves_worldsContiguousS4 φ₀ b e acc keys newBs newExps
    newAcc keys' hWC haK hstep⟩
  intro b' hb' e' he'
  exact
    { bClosure := modalStepBranchS4_preserves_bClosure φ₀ b e acc keys newBs newExps newAcc keys'
        hbC hWC hkT hkD hkI haK hstep b' hb'
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

/-! ## Keyed S4 Driver (Bespoke, Path (b))

Task 535 closes `Decidable (s4Valid φ)` via a bespoke, S4-specific `keys`-threaded driver, rather
than generalizing the shared generic driver (`Saturation.lean`'s `modalExpandBranchesGen`) to
thread opaque per-branch state -- that path would serve only S4 (K/T/B/S5/Five have all already
reached decidability via the state-free generic driver) while risking every one of their landed
proofs. `modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` below mirror
`modalExpandBranchesGen`/`processNext`/`modalTableauGen` structurally (copy-and-thread), with
`keys` (the stable per-world birth-key list `modalStepBranchS4Keyed` already threads) carried as
a fourth parallel worklist column alongside `(branch, expanded, acc)`. The live `modalTableauS4`
is left untouched as the reference artifact the `heq1`-style bridges and `modalHintikkaSetS4_eq`
consume; `instDecidableS4Valid` (Phase 5) points at `modalTableauS4Keyed` instead. -/

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

/-- The keyed S4 modal tableau decision procedure: the entry point for the bespoke keyed driver,
mirroring `modalTableauGen`/`modalTableauS4`'s entry-branch shape (`F(φ)@0`), with `keys := []`
at the start (no world has been born yet). Fuel is `modalFuelS4 φ`, the S4-specific fuel bound
(sufficiency: `modalExpMeasure_entry_le_fuelS4`) -- K's `modalFuel φ` is confirmed NOT provably
sufficient for the S4 keyed loop's pigeonhole world bound `modalWorldBoundS4`. The live
`modalTableauS4` is NOT redefined; `instDecidableS4Valid` (Phase 11) points at this declaration
instead. -/
def modalTableauS4Keyed (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) :=
    [⟨.neg, φ, 0⟩]
  modalExpandBranchesS4Keyed φ [initialBranch] [[]] [Accessibility.empty] [[]] (modalFuelS4 φ)

/-! ## Congruence Gate: `hintikka_congr_S4`

The sole genuinely-novel obligation of the keyed-driver path: the keyed rule
`modalApplyOneS4Keyed φ₀ keys` and the live rule `modalApplyOneS4 φ₀` agree on Hintikka-set-hood,
for ANY `keys`. Modeled on `hintikka_congr` (`S5Simplification.lean:604`). As with S5's witness
rule, the proof is unconditional (no saturation hypothesis needed): `modalHintikkaSetGen`'s
conjunct 2 (`Saturation.lean`) returns literal `True` at exactly the two shapes
(`F(□φ)@w`/`T(◇φ)@w`) where `modalApplyOneS4Keyed`/`modalApplyOneS4` can differ (the minting
guard shapes); at every OTHER shape, `modalApplyOneS4Keyed φ₀ keys` falls through to
`modalApplyOneS4 φ₀` by the definitional `| _, _ =>` catch-all, so `result` is the identical value
for both rules and conjunct 2 evaluates identically. Conjuncts 1/3/4 name no rule function at
all. -/

/-- **`hintikka_congr_S4`**: the keyed and live S4 rules agree on Hintikka-set-hood, for any
`keys`. -/
theorem hintikka_congr_S4 (φ₀ : Proposition Atom)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalHintikkaSetGen (modalApplyOneS4Keyed φ₀ keys) b acc ↔
      modalHintikkaSetGen (modalApplyOneS4 φ₀) b acc := by
  unfold modalHintikkaSetGen
  constructor <;> · rintro ⟨h1, h2, h3, h4⟩
                    refine ⟨h1, ?_, h3, h4⟩
                    intro sf hsf
                    have h := h2 sf hsf
                    rcases hs : sf.sign with _ | _ <;>
                      rcases hf : sf.formula with _|_|_|_|_|ψ|ψ <;>
                        simp_all [modalApplyOneS4Keyed]

/-! ## Keyed-Driver Termination Measure: Combinatorial Primitives

Territory-local re-derivations of the four generic `List.countP`-based combinatorial facts
underpinning the per-step measure decrease (`FmpMeasure.lean:2788-2922`). Those originals are
`private` and hence unreachable from this file; since the keyed S4 driver's territory is
additive-only within `LoopChecking.lean` (not an edit to `FmpMeasure.lean`), the four lemmas are
re-derived here verbatim (same proofs, `_S4`-suffixed names) rather than exposed upstream. -/

/-- **Combinatorial core** (generic over any `BEq`/`LawfulBEq` type, mirroring
`modalCount_notMem_append_drop`, `FmpMeasure.lean:2788`): appending `x` (a member of `U`, not yet
in `l`) to the exclusion list `l` strictly drops, by at least one, the count of `U`-members
excluded by `l`. -/
private lemma modalCount_notMem_append_drop_S4
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

/-- **Weak monotonicity** (mirroring `modalCount_notMem_mono`, `FmpMeasure.lean:2865`): growing
the exclusion list's underlying membership set (`b ⊆ b'`) can only decrease (never increase) the
count of `U`-members excluded by it. -/
private lemma modalCount_notMem_mono_S4
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
/-- **`R`-drop, linear/branching case** (mirroring `modalWork_drop_linear`,
`FmpMeasure.lean:2887`): when the fired formula `sf` is added to the expanded set
(`e' = e ++ [sf]`) and the child branch `b'` weakly extends `b`, the counting measure strictly
drops by at least one. -/
private lemma modalWork_drop_linear_S4
    (U b b' e : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hsfU : sf ∈ U) (hsfe : e.any (· == sf) = false) (hsub : ∀ z ∈ b, z ∈ b') :
    modalWork U b' (e ++ [sf]) + 1 ≤ modalWork U b e := by
  unfold modalWork
  have hb := modalCount_notMem_mono_S4 U b b' hsub
  have he := modalCount_notMem_append_drop_S4 U e sf hsfU hsfe
  omega

omit [Hashable Atom] in
/-- **`R`-drop, persistent case** (mirroring `modalWork_drop_persistent`,
`FmpMeasure.lean:2904`): when the expanded set is unchanged (`boxPos`/`diamondNeg`) but the child
branch `b'` contains a fresh `U`-member `x0` not on `b`, the counting measure strictly drops by
at least one. -/
private lemma modalWork_drop_persistent_S4
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
  have hmono := modalCount_notMem_mono_S4 U (b ++ [x0]) b' hstep
  have hx0notin : b.any (· == x0) = false := by
    rw [Bool.eq_false_iff]
    intro hcon
    obtain ⟨z, hz, heq⟩ := List.any_eq_true.mp hcon
    exact hx0b ((LawfulBEq.eq_of_beq heq) ▸ hz)
  have hdrop := modalCount_notMem_append_drop_S4 U b x0 hx0U hx0notin
  omega

/-! ## Keyed-Driver Termination Measure: Per-Call Obligations for `modalApplyOneS4Keyed`

The three raw measure-step hypotheses (`hBranchingLength`/`hPersistentFresh`/
`hOutputsSubsetUniverse`, the shape consumed by `modalExpMeasure_step_lt_gen`,
`FmpMeasure.lean:3227-3246`) as S4Keyed analogues, each universally quantified over `keys` so a
single lemma serves every fuel step. Built by the same mint-blocked/mint-unblocked/non-mint case
split as `modalStepBranchS4_preserves_bClosure`. The T-rule/4-rule propagation arms
(`modalTBoxSelf`/`modalTDiaNegSelf`/`modalFourBoxProp`/`modalFourDiaNegProp`, `FrameRules.lean`)
never appear in K's own dispatch, so their persistent-freshness is new content, established here
via their shared filter-guard shape (mirroring `diamondNeg_filterMap_fresh`,
`FmpMeasure.lean:3032`). -/

omit [Hashable Atom] in
/-- `modalTBoxSelf`'s nonempty branch is exactly `[sf]` with `sf ∉ b` by the guard itself. -/
private lemma modalTBoxSelf_fresh
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ modalTBoxSelf b φ w, x ∉ b := by
  simp only [modalTBoxSelf]
  split_ifs with h
  · simp
  · simp only [List.mem_singleton]
    rintro x rfl
    simp only [Bool.not_eq_true] at h
    rw [List.any_eq_false] at h
    exact fun hxb => h _ hxb (by simp)

omit [Hashable Atom] in
/-- `modalTDiaNegSelf`'s nonempty branch is exactly `[sf]` with `sf ∉ b`. Dual of
`modalTBoxSelf_fresh`. -/
private lemma modalTDiaNegSelf_fresh
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ modalTDiaNegSelf b φ w, x ∉ b := by
  simp only [modalTDiaNegSelf]
  split_ifs with h
  · simp
  · simp only [List.mem_singleton]
    rintro x rfl
    simp only [Bool.not_eq_true] at h
    rw [List.any_eq_false] at h
    exact fun hxb => h _ hxb (by simp)

omit [Hashable Atom] in
/-- Every formula `modalFourBoxProp` emits is fresh (`∉ b`), by the same `filterMap` guard
technique as `diamondNeg_filterMap_fresh` (`FmpMeasure.lean:3032`). -/
private lemma modalFourBoxProp_fresh
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ modalFourBoxProp b acc φ w, x ∉ b := by
  intro x hx
  simp only [modalFourBoxProp, List.mem_filterMap] at hx
  obtain ⟨w', -, hxeq⟩ := hx
  split_ifs at hxeq with hcond
  · simp only [Option.some.injEq] at hxeq
    subst hxeq
    intro hxb
    simp only [Bool.not_eq_true] at hcond
    rw [List.any_eq_false] at hcond
    exact hcond _ hxb (by simp)

omit [Hashable Atom] in
/-- Every formula `modalFourDiaNegProp` emits is fresh (`∉ b`). Dual of
`modalFourBoxProp_fresh`. -/
private lemma modalFourDiaNegProp_fresh
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    ∀ x ∈ modalFourDiaNegProp b acc φ w, x ∉ b := by
  intro x hx
  simp only [modalFourDiaNegProp, List.mem_filterMap] at hx
  obtain ⟨w', -, hxeq⟩ := hx
  split_ifs at hxeq with hcond
  · simp only [Option.some.injEq] at hxeq
    subst hxeq
    intro hxb
    simp only [Bool.not_eq_true] at hcond
    rw [List.any_eq_false] at hcond
    exact hcond _ hxb (by simp)

omit [Hashable Atom] in
/-- **Persistent-rule nonemptiness/freshness for `modalApplyOneT`** (T-augmented K): whenever
`modalApplyOneT sf b acc` produces a `.persistent` result, the emitted formulas are nonempty and
fresh. At the two T-relevant shapes (`T(□φ)@w`/`F(◇φ)@w`), composes K's own
`modalApplyOne_persistent_props` with `modalTBoxSelf_fresh`/`modalTDiaNegSelf_fresh`; at every
other shape `modalApplyOneT` reduces to `modalApplyOne` directly
(`modalApplyOneT_eq_of_not_boxPos_diaNeg`), so K's fact applies unchanged. -/
private lemma modalApplyOneT_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneT sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneT at hca
    dsimp only at hca
    rcases hk : (modalApplyOne (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      simp only [RuleResult.persistent.injEq] at hca
      obtain ⟨hkf, hkfresh⟩ := modalApplyOne_persistent_props _ b acc kf hk
      have hself := modalTBoxSelf_fresh b ψ sf.label
      refine ⟨?_, ?_⟩
      · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil hkf _
      · intro x hx
        rw [← hca] at hx
        rcases List.mem_append.mp hx with hxk | hxs
        · exact hkfresh x hxk
        · exact hself x (List.mem_of_mem_filter hxs)
    · rw [hk] at hca
      dsimp only at hca
      split_ifs at hca with hemp
      · simp only [RuleResult.persistent.injEq] at hca
        refine ⟨?_, ?_⟩
        · rw [← hca]; simp only [Bool.not_eq_true] at hemp
          exact List.isEmpty_eq_false_iff.mp hemp
        · intro x hx; rw [← hca] at hx; exact modalTBoxSelf_fresh b ψ sf.label x hx
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneT at hca
      dsimp only at hca
      rcases hk : (modalApplyOne (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        simp only [RuleResult.persistent.injEq] at hca
        obtain ⟨hkf, hkfresh⟩ := modalApplyOne_persistent_props _ b acc kf hk
        have hself := modalTDiaNegSelf_fresh b ψ sf.label
        refine ⟨?_, ?_⟩
        · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil hkf _
        · intro x hx
          rw [← hca] at hx
          rcases List.mem_append.mp hx with hxk | hxs
          · exact hkfresh x hxk
          · exact hself x (List.mem_of_mem_filter hxs)
      · rw [hk] at hca
        dsimp only at hca
        split_ifs at hca with hemp
        · simp only [RuleResult.persistent.injEq] at hca
          refine ⟨?_, ?_⟩
          · rw [← hca]; simp only [Bool.not_eq_true] at hemp
            exact List.isEmpty_eq_false_iff.mp hemp
          · intro x hx; rw [← hca] at hx; exact modalTDiaNegSelf_fresh b ψ sf.label x hx
    · have heq : modalApplyOneT sf b acc = modalApplyOne sf b acc :=
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOne_persistent_props sf b acc nf hca

omit [Hashable Atom] in
/-- **Branching-length for `modalApplyOneT`**: `modalApplyOneT` never introduces branching at
the two T-relevant shapes (K's own dispatch is `persistent`/`notApplicable` only there, and the
T-merge never turns either into `.branching`), so any `.branching` result must come from the
`_,_` fallthrough, i.e. from `modalApplyOne` directly, where K's own
`modalApplyOne_branching_length` applies. -/
private lemma modalApplyOneT_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneT sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneT at hca
    dsimp only at hca
    rcases hk : (modalApplyOne (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      dsimp only at hca
      simp only [RuleResult.branching.injEq] at hca
      rw [← hca]
      exact modalApplyOne_branching_length _ b acc kbrs hk
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      dsimp only at hca
      split_ifs at hca
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneT at hca
      dsimp only at hca
      rcases hk : (modalApplyOne (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        dsimp only at hca
        simp only [RuleResult.branching.injEq] at hca
        rw [← hca]
        exact modalApplyOne_branching_length _ b acc kbrs hk
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        dsimp only at hca
        split_ifs at hca
    · have heq : modalApplyOneT sf b acc = modalApplyOne sf b acc :=
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOne_branching_length sf b acc brs hca

omit [Hashable Atom] in
/-- **Persistent-rule nonemptiness/freshness for `modalApplyOneS4Rules`** (T+4-augmented K):
same recipe as `modalApplyOneT_persistentFresh`, one layer up -- composes
`modalApplyOneT_persistentFresh` with `modalFourBoxProp_fresh`/`modalFourDiaNegProp_fresh` at the
two 4-relevant shapes, and reduces to `modalApplyOneT` directly elsewhere
(`modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg`). -/
private lemma modalApplyOneS4Rules_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneS4Rules sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneS4Rules at hca
    dsimp only at hca
    rcases ht : (modalApplyOneT (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      simp only [RuleResult.persistent.injEq] at hca
      obtain ⟨htf, htfresh⟩ := modalApplyOneT_persistentFresh _ b acc tf ht
      have hfour := modalFourBoxProp_fresh b acc ψ sf.label
      refine ⟨?_, ?_⟩
      · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil htf _
      · intro x hx
        rw [← hca] at hx
        rcases List.mem_append.mp hx with hxt | hxs
        · exact htfresh x hxt
        · exact hfour x (List.mem_of_mem_filter hxs)
    · rw [ht] at hca
      dsimp only at hca
      split_ifs at hca with hemp
      · simp only [RuleResult.persistent.injEq] at hca
        refine ⟨?_, ?_⟩
        · rw [← hca]; simp only [Bool.not_eq_true] at hemp
          exact List.isEmpty_eq_false_iff.mp hemp
        · intro x hx; rw [← hca] at hx; exact modalFourBoxProp_fresh b acc ψ sf.label x hx
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneS4Rules at hca
      dsimp only at hca
      rcases ht : (modalApplyOneT (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        simp only [RuleResult.persistent.injEq] at hca
        obtain ⟨htf, htfresh⟩ := modalApplyOneT_persistentFresh _ b acc tf ht
        have hfour := modalFourDiaNegProp_fresh b acc ψ sf.label
        refine ⟨?_, ?_⟩
        · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil htf _
        · intro x hx
          rw [← hca] at hx
          rcases List.mem_append.mp hx with hxt | hxs
          · exact htfresh x hxt
          · exact hfour x (List.mem_of_mem_filter hxs)
      · rw [ht] at hca
        dsimp only at hca
        split_ifs at hca with hemp
        · simp only [RuleResult.persistent.injEq] at hca
          refine ⟨?_, ?_⟩
          · rw [← hca]; simp only [Bool.not_eq_true] at hemp
            exact List.isEmpty_eq_false_iff.mp hemp
          · intro x hx; rw [← hca] at hx
            exact modalFourDiaNegProp_fresh b acc ψ sf.label x hx
    · have heq : modalApplyOneS4Rules sf b acc = modalApplyOneT sf b acc :=
        modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOneT_persistentFresh sf b acc nf hca

omit [Hashable Atom] in
/-- **Branching-length for `modalApplyOneS4Rules`**: same argument as
`modalApplyOneT_branchingLength`, one layer up. -/
private lemma modalApplyOneS4Rules_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneS4Rules sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneS4Rules at hca
    dsimp only at hca
    rcases ht : (modalApplyOneT (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      dsimp only at hca
      simp only [RuleResult.branching.injEq] at hca
      rw [← hca]
      exact modalApplyOneT_branchingLength _ b acc tbrs ht
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      dsimp only at hca
      split_ifs at hca
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneS4Rules at hca
      dsimp only at hca
      rcases ht : (modalApplyOneT (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        dsimp only at hca
        simp only [RuleResult.branching.injEq] at hca
        rw [← hca]
        exact modalApplyOneT_branchingLength _ b acc tbrs ht
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        dsimp only at hca
        split_ifs at hca
    · have heq : modalApplyOneS4Rules sf b acc = modalApplyOneT sf b acc :=
        modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOneT_branchingLength sf b acc brs hca

/-- **`hPersistentFresh` obligation for `modalApplyOneS4Keyed`**, for any `keys`: mint-blocked
gives `.linear []` (vacuous, never `.persistent`); mint-unblocked reduces to raw `modalApplyOne`
(K's own `modalApplyOne_persistent_props` applies directly); non-mint reduces to
`modalApplyOneS4Rules` (`modalApplyOneS4Rules_persistentFresh` applies). -/
private lemma modalApplyOneS4Keyed_persistentFresh_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneS4Keyed φ₀ keys sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2] at hca
        exact modalApplyOne_persistent_props _ b acc nf hca
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2] at hca
        exact modalApplyOne_persistent_props _ b acc nf hca
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
      unfold modalApplyOneS4Keyed
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
        simp_all
    rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hnbd] at hca
    by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exact modalApplyOneS4Rules_persistentFresh sf b acc nf hca
    · have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
      rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd2,
          modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd2] at hca
      exact modalApplyOne_persistent_props sf b acc nf hca

/-- **`hBranchingLength` obligation for `modalApplyOneS4Keyed`**, for any `keys`: same
mint-blocked/mint-unblocked/non-mint split as `modalApplyOneS4Keyed_persistentFresh_S4`. -/
private lemma modalApplyOneS4Keyed_branchingLength_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneS4Keyed φ₀ keys sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2] at hca
        exact modalApplyOne_branching_length _ b acc brs hca
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2] at hca
        exact modalApplyOne_branching_length _ b acc brs hca
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
      unfold modalApplyOneS4Keyed
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
        simp_all
    rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hnbd] at hca
    by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exact modalApplyOneS4Rules_branchingLength sf b acc brs hca
    · have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
      rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd2,
          modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd2] at hca
      exact modalApplyOne_branching_length sf b acc brs hca

/-- **`hOutputsSubsetUniverse` obligation for `modalApplyOneS4Keyed`**, assembled from the
mint-unblocked outputs-subset facts (`modalApplyOne_boxNeg_outputs_subset_S4`/
`modalApplyOne_diamondPos_outputs_subset_S4`, needing the STRICT world bound `hW`, supplied by
`modalStepBranchS4_worldBound`), the vacuous mint-blocked case, and the already-landed
`modalApplyOneS4Keyed_nonMint_universe_S4` for the 12 non-minting shapes. Mirrors
`modalStepBranchS4_preserves_bClosure`'s case split exactly, concluding the raw universe-subset
match fact instead of branch-closure. -/
private lemma modalApplyOneS4Keyed_outputsSubsetUniverse_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀) (hsfmem : sf ∈ b)
    (hknown : accTargetsKnown b acc)
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    (match (modalApplyOneS4Keyed φ₀ keys sf b acc).fst with
      | .linear fs => ∀ x ∈ fs, x ∈ modalUniverseS4 φ₀
      | .branching brs => ∀ x ∈ brs.flatten, x ∈ modalUniverseS4 φ₀
      | .persistent fs => ∀ x ∈ fs, x ∈ modalUniverseS4 φ₀
      | .notApplicable => True) := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
    rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
      rw [hsfeq]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, modalApplyOne_boxNeg_mint_fst_S4 b acc ψ sf.label]
        exact modalApplyOne_boxNeg_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2]; simp
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
      rw [hsfeq]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, modalApplyOne_diamondPos_mint_fst_S4 b acc ψ sf.label]
        exact modalApplyOne_diamondPos_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2]; simp
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    exact modalApplyOneS4Keyed_nonMint_universe_S4 φ₀ keys sf b acc hb hsfmem hknown hnbd

/-! ## Keyed-Driver Termination Measure: Entry-Measure Sufficiency for `modalFuelS4`

`modalFuel φ₀` (K's fuel) is confirmed NOT provably sufficient for the S4 keyed loop: at
`modalComplexity φ₀ = 0`, `modalWorldBoundS4 φ₀ = 2 ^ (2 * 1) = 4` exceeds K's
`modalWorldBound φ₀ = 1`. The dedicated `modalFuelS4` (defined earlier, alongside
`modalWorldBoundS4`/`modalUniverseS4`, so it is in scope for `modalTableauS4Keyed`'s fuel
argument) is shown sufficient here, mirroring `modalExpMeasure_entry_le_fuel`
(`FmpMeasure.lean:208-251`). -/

/-- **Entry-measure sufficiency for `modalFuelS4`**: at the S4 keyed tableau's entry point, the
worklist measure over `modalUniverseS4 φ₀` is bounded by `modalFuelS4 φ₀`. Direct transcription
of `modalExpMeasure_entry_le_fuel` (`FmpMeasure.lean:208-251`), substituting `modalUniverseS4`/
`modalWorldBoundS4`/`modalUniverseS4_length_le` for their K counterparts -- the
`modalWork ≤ 2 * U.length` step is universe-agnostic (`List.countP_le_length` + `simp` on the
empty expanded-set case), so it transfers verbatim. -/
lemma modalExpMeasure_entry_le_fuelS4 (φ₀ : Proposition Atom) :
    modalExpMeasure (modalUniverseS4 φ₀) [[(⟨.neg, φ₀, 0⟩ :
      SignedFormula (Proposition Atom) WorldIndex)]] [[]] ≤ modalFuelS4 φ₀ := by
  have hmeas : modalExpMeasure (modalUniverseS4 φ₀)
      [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      = 3 ^ modalWork (modalUniverseS4 φ₀)
          [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] := by
    simp [modalExpMeasure]
  rw [hmeas]
  have hwork : modalWork (modalUniverseS4 φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 2 * (modalUniverseS4 φ₀).length := by
    unfold modalWork
    have h1 : (modalUniverseS4 φ₀).countP
        (fun sf => !(([(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]).any
          (· == sf))) ≤ (modalUniverseS4 φ₀).length :=
      List.countP_le_length
    have h2 : (modalUniverseS4 φ₀).countP
        (fun sf => !((([] : List (SignedFormula (Proposition Atom) WorldIndex))).any
          (· == sf))) = (modalUniverseS4 φ₀).length := by
      simp
    omega
  have hUlen := modalUniverseS4_length_le φ₀
  have hfinal : modalWork (modalUniverseS4 φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] ≤
      4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by
    have h2U : 2 * (modalUniverseS4 φ₀).length ≤
        2 * (2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) :=
      Nat.mul_le_mul_left 2 hUlen
    have heq : 2 * (2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) =
        4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by ring
    rw [heq] at h2U
    omega
  calc 3 ^ modalWork (modalUniverseS4 φ₀)
        [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 3 ^ (4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) :=
        Nat.pow_le_pow_right (by norm_num) hfinal
    _ = modalFuelS4 φ₀ := rfl

/-! ## Phase 6 (handoff 3d-i): Keys-Threaded Hintikka-Tracking Invariant Bundle

The bespoke keys-threaded analogue of the `ModalLoopInvHintikka` bundle
(`CompletenessLoop.lean:293-325`), for `modalApplyOneS4Keyed φ₀ keys`. `S4LoopInv` (task 511,
frozen, above) already carries the universe-closure/keys-bookkeeping conjuncts
(`bClosure`/`eClosure`/`eNodup`/`accFresh`/`accKnown`), so this bundle carries ONLY the five
Hintikka-specific conjuncts (`hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`/`eDiamondOnlyPos`/
`eDiamondPosWitness`), threaded alongside `S4LoopInv` as a separate ambient hypothesis at each
call site rather than duplicating its fields. -/

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

/-- **Territory-local re-derivation of `modalHintikkaClauseGen_lift`** (`private` to
`Completeness.lean`, hence unavailable here, per Phase 3's re-derivation precedent): if
`modalHintikkaClauseGen apply s φ w b acc` holds and `b ⊆ b'`, it holds at `(b', acc')` too,
given `apply`'s F8 local-shape-invariance. Verbatim transcription of the generic proof, kept
generic in `apply` (rather than specialized to `modalApplyOneS4Keyed`) for direct auditability
against its source. -/
private lemma modalHintikkaClauseGen_lift_S4
    (apply : RuleApply Atom)
    (hLocalShapeInvariance : ∀ (s : Sign) (φ : Proposition Atom) (w : WorldIndex),
      (∀ ψ, φ ≠ .box ψ) → (∀ ψ, φ ≠ .diamond ψ) →
      ∀ (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
        (acc acc' : Accessibility),
      (apply ⟨s, φ, w⟩ b acc).1 = (apply ⟨s, φ, w⟩ b' acc').1)
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) (hsub : b ⊆ b')
    (hInv : modalHintikkaClauseGen apply s φ w b acc) :
    modalHintikkaClauseGen apply s φ w b' acc' := by
  unfold modalHintikkaClauseGen at hInv ⊢
  rcases φ with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
  · have heq := hLocalShapeInvariance s (.atom p) w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .atom p, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := hLocalShapeInvariance s .bot w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .bot, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := hLocalShapeInvariance s (.imp a c) w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .imp a c, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := hLocalShapeInvariance s (.and x y) w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .and x y, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := hLocalShapeInvariance s (.or x y) w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .or x y, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · trivial
  · trivial

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
private lemma modalApplyOneS4Rules_snd_eq (sf : SignedFormula (Proposition Atom) WorldIndex)
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
      · rw [modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock]
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
      · rw [modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock]
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

/-- **Keys-threaded Hintikka-tracking invariant bundle** for `modalApplyOneS4Keyed φ₀ keys`: the
bespoke analogue of `ModalLoopInvHintikka`'s five Hintikka-specific conjuncts
(`CompletenessLoop.lean:310-325`), carrying ONLY those five fields. The universe-closure/
keys-bookkeeping conjuncts already live in the frozen `S4LoopInv` (task 511) and are threaded as
a separate ambient hypothesis at each call site rather than duplicated here. -/
structure S4KeyedHintikkaInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop where
  /-- Every already-expanded formula's Hintikka witness obligation is already met on `b`. -/
  hintikkaInv : ∀ sf ∈ e,
    modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys) sf.sign sf.formula sf.label b acc
  /-- Every box-shaped formula in the expanded set `e` has sign `.neg`. -/
  eBoxOnlyNeg : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg
  /-- Every `boxNeg`-shaped formula already has a witness successor on the branch. -/
  eBoxNegWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
  /-- Every diamond-shaped formula in the expanded set `e` has sign `.pos`. -/
  eDiamondOnlyPos : ∀ sf ∈ e, ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos
  /-- Every `diamondPos`-shaped formula already has a witness successor on the branch. -/
  eDiamondPosWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b

/-- **`S4KeyedHintikkaInv` weakens across branch/accessibility growth** at a FIXED expanded set
`e`: this discharges Phase 6's monotonicity obligations directly --
`hintikkaInv` transports via the branch/`acc`-independence of non-box/diamond shapes
(`modalHintikkaClauseGen_lift_S4` fed `modalApplyOneS4Keyed_fst_eq_of_not_box`; box/diamond
shapes are vacuously `True` on both sides), and the two witness-existence fields are permanent
once recorded since `acc`/`b` only grow (`hbsub`/`haccsub`). `eBoxOnlyNeg`/`eDiamondOnlyPos`
mention no `b`/`acc` at all and transport unchanged. This is the building block Phase 7's
single-step preservation composes against the OLD `e`'s facts lifted to the post-step
`(b', acc')`. -/
lemma S4KeyedHintikkaInv_weaken (φ₀ : Proposition Atom)
    (b b' e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc acc' : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hbsub : b ⊆ b')
    (haccsub : ∀ w w', acc.hasEdge w w' = true → acc'.hasEdge w w' = true)
    (hinv : S4KeyedHintikkaInv φ₀ b e acc keys) :
    S4KeyedHintikkaInv φ₀ b' e acc' keys := by
  refine ⟨?_, hinv.eBoxOnlyNeg, ?_, hinv.eDiamondOnlyPos, ?_⟩
  · intro sf hsf
    exact modalHintikkaClauseGen_lift_S4 (modalApplyOneS4Keyed φ₀ keys)
      (modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys) sf.sign sf.formula sf.label b b' acc acc'
      hbsub (hinv.hintikkaInv sf hsf)
  · intro sf hsf ψ w hsfeq
    obtain ⟨w', hedge, hwit⟩ := hinv.eBoxNegWitness sf hsf ψ w hsfeq
    exact ⟨w', haccsub w w' hedge, hbsub hwit⟩
  · intro sf hsf ψ w hsfeq
    obtain ⟨w', hedge, hwit⟩ := hinv.eDiamondPosWitness sf hsf ψ w hsfeq
    exact ⟨w', haccsub w w' hedge, hbsub hwit⟩

/-! ## Phase 7: Single-Step Invariant Preservation -/

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
private lemma modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding (φ₀ : Proposition Atom)
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

/-- `modalApplyOneS4Keyed φ₀ keys sf b acc` at a non-box/diamond-shaped `sf` is exactly raw
K's `modalApplyOne sf b acc`, for ANY `keys` -- the dispatch chain `modalApplyOneS4Keyed →
modalApplyOneS4 → modalApplyOneS4Rules → modalApplyOneT → modalApplyOne` fires its catch-all arm
at every layer (mirrors the internal `hred` fact inside `modalApplyOneS4Keyed_fst_eq_of_not_box`,
extracted standalone since that lemma only exposes the branch/`acc`-invariance corollary, not the
underlying `keys`-independence). -/
private lemma modalApplyOneS4Keyed_eq_modalApplyOne_of_not_box (φ₀ : Proposition Atom)
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
shape (`modalApplyOneS4Keyed_keys_indep_of_not_box`). This is exactly what lets Phase 7's single-
step preservation lift the OLD `e`'s `hintikkaInv` facts (stated over `keys`) to the post-step
`keys'` without re-deriving anything about the individual formulas of `e`. -/
private lemma modalHintikkaClauseGen_S4Keyed_keys_indep (φ₀ : Proposition Atom)
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

/-- **Assembly helper**: given the OLD `e`'s bundle already transported to the post-step
`(b', acc')` at the OLD `keys` (`S4KeyedHintikkaInv_weaken`), plus the just-selected formula
`sf`'s own five per-field facts at the post-step `keys'`, assemble the full bundle at
`e ++ [sf]`. The old-`e` facts are lifted from `keys` to `keys'` via
`modalHintikkaClauseGen_S4Keyed_keys_indep` (only `hintikkaInv` mentions `keys`; the other four
fields do not reference `apply`/`keys` at all). -/
private lemma S4KeyedHintikkaInv_append (φ₀ : Proposition Atom)
    (b' e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc' : Accessibility)
    (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hweak : S4KeyedHintikkaInv φ₀ b' e acc' keys)
    (hnew_hintikka : modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys') sf.sign sf.formula
      sf.label b' acc')
    (hnew_boxOnlyNeg : ∀ ψ, sf.formula = .box ψ → sf.sign = .neg)
    (hnew_diaOnlyPos : ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos)
    (hnew_boxNegWitness : ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc'.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b')
    (hnew_diaPosWitness : ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc'.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b') :
    S4KeyedHintikkaInv φ₀ b' (e ++ [sf]) acc' keys' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sf' hsf'
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · rw [← modalHintikkaClauseGen_S4Keyed_keys_indep φ₀ keys keys' sf'.sign sf'.formula
        sf'.label b' acc']
      exact hweak.hintikkaInv sf' hold
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_hintikka
  · intro sf' hsf' ψ hform
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eBoxOnlyNeg sf' hold ψ hform
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_boxOnlyNeg ψ hform
  · intro sf' hsf' ψ w hsfeq
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eBoxNegWitness sf' hold ψ w hsfeq
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_boxNegWitness ψ w hsfeq
  · intro sf' hsf' ψ hform
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eDiamondOnlyPos sf' hold ψ hform
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_diaOnlyPos ψ hform
  · intro sf' hsf' ψ w hsfeq
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eDiamondPosWitness sf' hold ψ w hsfeq
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_diaPosWitness ψ w hsfeq

/-- **Phase 7 — single-step preservation of `S4KeyedHintikkaInv`**: every
`modalStepBranchS4Keyed` step preserves the keys-threaded Hintikka-tracking invariant bundle,
given the ambient `S4LoopInv` (task 511, consumed for `keyLowerBd`'s blocked-witness argument).
Mirrors `modalStepBranchS4_preserves_bClosure`'s case-split shape (mint-unblocked / mint-blocked
/ non-mint), composing `S4KeyedHintikkaInv_weaken` (Phase 6, old `e`'s facts lifted across
branch/`acc` growth) with `S4KeyedHintikkaInv_append`'s per-field assembly for the just-selected
formula: an unblocked mint discharges its witness via K's own `modalApplyOne_boxNeg_witness`/
`_diamondPos_witness`; a blocked redirect discharges it via
`modalStepBranchS4Keyed_blocked_witness_mem` (this file, Phase 7). -/
theorem modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hLoopInv : S4LoopInv φ₀ b e acc keys)
    (hHinv : S4KeyedHintikkaInv φ₀ b e acc keys)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, S4KeyedHintikkaInv φ₀ b' e' newAcc keys' := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  have haccsub : ∀ w w', acc.hasEdge w w' = true → newAcc0.hasEdge w w' = true := by
    intro w w' h
    have hmono := modalApplyOneS4Keyed_hasEdge_mono φ₀ keys sf b acc h
    rwa [hpair] at hmono
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · -- neg + box: the boxNeg minting shape.
      have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · -- unblocked: fresh witness world, standard K minting facts transfer.
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOne_boxNeg_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, -⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b
          (((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            rest) ++ b) e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label (modalNextWorld b) = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        refine S4KeyedHintikkaInv_append φ₀ _ e newAcc0 keys keys'
          (⟨.neg, .box ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' _; rfl
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.box.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨modalNextWorld b, hedge, List.mem_append_left _ List.mem_cons_self⟩
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
      · -- blocked: redirect to `wBlock`, witness already on the branch.
        have hAOeq := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        rw [hb', he']
        subst hnewAcc; subst hnewKeys
        have hbsub : ∀ x ∈ b, x ∈ b := fun x hx => hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b b e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label wBlock = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        have hwitmem := modalStepBranchS4Keyed_blocked_witness_mem φ₀ b keys .neg ψ sf.label
          wBlock hLoopInv.keyLowerBd hblock
        refine S4KeyedHintikkaInv_append φ₀ b e newAcc0 keys keys
          (⟨.neg, .box ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' _; rfl
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.box.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨wBlock, hedge, hwitmem⟩
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
    · -- pos + diamond: the diamondPos minting shape, symmetric to neg + box above.
      have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · -- unblocked: fresh witness world.
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOne_diamondPos_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, -⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b
          (((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            rest) ++ b) e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label (modalNextWorld b) = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        refine S4KeyedHintikkaInv_append φ₀ _ e newAcc0 keys keys'
          (⟨.pos, .diamond ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' _; rfl
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.diamond.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨modalNextWorld b, hedge, List.mem_append_left _ List.mem_cons_self⟩
      · -- blocked: redirect to `wBlock`.
        have hAOeq := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        rw [hb', he']
        subst hnewAcc; subst hnewKeys
        have hbsub : ∀ x ∈ b, x ∈ b := fun x hx => hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b b e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label wBlock = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        have hwitmem := modalStepBranchS4Keyed_blocked_witness_mem φ₀ b keys .pos ψ sf.label
          wBlock hLoopInv.keyLowerBd hblock
        refine S4KeyedHintikkaInv_append φ₀ b e newAcc0 keys keys
          (⟨.pos, .diamond ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' _; rfl
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.diamond.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨wBlock, hedge, hwitmem⟩
  · -- non-mint: `sf` is neither the boxNeg nor the diaPos minting shape, so `keys' = keys`
    -- (the `keys'`-defining match falls to its `_, _` catch-all). `result` is
    -- `.persistent`/`.linear`/`.branching` for a purely propositional or T/4-persistent `sf`;
    -- `.notApplicable` is excluded since `findSome?` only returns `some` there.
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    rw [hpair] at hsf
    dsimp only at hsf
    by_cases hmint2 : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · -- pos-box / neg-diamond: always persistent/notApplicable (never linear/branching).
      have hne := modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding φ₀ keys sf b acc hsfmem
        hLoopInv.accKnown hmint2
      rw [hpair] at hne
      dsimp only at hne
      rcases hres : result with lf | brs | lf | _
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
    · -- genuinely propositional: `sf.formula` is neither box- nor diamond-shaped at all.
      have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => hmint2 (Or.inl hc), fun hc => hmint2 (Or.inr hc)⟩
      have hnb : ∀ ψ, sf.formula ≠ .box ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd2.1 ⟨hs, ψ, hform⟩
        · exact hnbd.1 ⟨hs, ψ, hform⟩
      have hnd : ∀ ψ, sf.formula ≠ .diamond ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd.2 ⟨hs, ψ, hform⟩
        · exact hnbd2.2 ⟨hs, ψ, hform⟩
      rcases hres : result with lf | brs | lf | _
      · -- linear (propositional rule, e.g. and/or/imp)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (lf ++ b) newAcc0).1 = RuleResult.linear lf := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (lf ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        refine S4KeyedHintikkaInv_append φ₀ (lf ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- branching (propositional or-rule)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'
        obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
        rw [← hnewExps] at he'
        obtain ⟨br', hbr'mem, he'eq⟩ := List.mem_map.mp he'
        subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ br ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (br ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (br ++ b) newAcc0).1 = RuleResult.branching brs := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (br ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        rw [← he'eq]
        refine S4KeyedHintikkaInv_append φ₀ (br ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- persistent (no change to `e`)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · -- notApplicable: impossible, `findSome?` only returns `some` when applicable.
        rw [hres] at hsf; simp at hsf

/-! ## Phase 8: 4-Tuple Stepper Projection Bridge + Local Measure-Split Helpers

The measure-decrease engine (`modalExpMeasure_step_lt_gen`, `FmpMeasure.lean:3227`) is phrased
against the generic 3-tuple driver `modalStepBranchGen` (`Saturation.lean:122`), whereas the
keyed S4 driver `modalStepBranchS4Keyed` returns a 4-tuple with `keys'` bolted on. This section
bridges the two: `modalStepBranchS4Keyed_proj_stepBranchGen` shows a keyed step implies the
corresponding generic step at `apply := modalApplyOneS4Keyed φ₀ keys`, dropping the `keys'`
component. Both drivers scan the same branch `b` via `List.findSome?` with the same
"already expanded" guard and the same four `RuleResult` arms, so this is a structural
`findSome?`-congruence argument, not a semantic one. -/

/-- **Generic `findSome?` projection helper**: if a list-scan via `g1` (into a 4-tuple type
`A × B × Accessibility × K`) succeeds pointwise-projecting to a scan via `g2` (into the
3-tuple `A × B × Accessibility`, dropping the last component whenever `g1` is `some`, and
agreeing with `g1` on which elements are skipped/`none`), then `g1`'s scan result projects to
`g2`'s scan result the same way. Purely structural: no reference to any tableau-specific type. -/
private lemma stepBranch_findSome?_proj4to3
    {α A B K : Type*}
    {g1 : α → Option (A × B × Accessibility × K)}
    {g2 : α → Option (A × B × Accessibility)}
    (hpt : ∀ (x : α) (a : A) (bb : B) (c : Accessibility) (k : K),
      g1 x = some (a, bb, c, k) → g2 x = some (a, bb, c))
    (hnone : ∀ x : α, g1 x = none → g2 x = none) :
    ∀ (l : List α) (a : A) (bb : B) (c : Accessibility) (k : K),
      l.findSome? g1 = some (a, bb, c, k) → l.findSome? g2 = some (a, bb, c) := by
  intro l
  induction l with
  | nil => intro a bb c k h; simp at h
  | cons x rest ih =>
    intro a bb c k h
    rw [List.findSome?_cons] at h
    rw [List.findSome?_cons]
    cases hg1 : g1 x with
    | none =>
      rw [hg1] at h
      rw [hnone x hg1]
      exact ih a bb c k h
    | some v =>
      rw [hg1] at h
      simp only [Option.some.injEq] at h
      have hg1' : g1 x = some (a, bb, c, k) := by rw [hg1, h]
      rw [hpt x a bb c k hg1']

/-- **The projection lemma (Phase 8)**: a keyed step at `modalStepBranchS4Keyed φ₀ b e acc keys`
implies the corresponding step of the generic driver at `apply := modalApplyOneS4Keyed φ₀ keys`,
dropping the `keys'` component. Both sides select the SAME formula `sf` from `b` (same
"already expanded" guard `e.any (· == sf)`) and dispatch on the SAME `RuleResult` value
`(modalApplyOneS4Keyed φ₀ keys sf b acc).1`, since `modalStepBranchGen`'s `apply sf b acc` at
`apply := modalApplyOneS4Keyed φ₀ keys` computes literally the same pair the keyed stepper
computes internally. -/
lemma modalStepBranchS4Keyed_proj_stepBranchGen (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys) b e acc = some (newBs, newExps, newAcc) := by
  unfold modalStepBranchS4Keyed at hstep
  unfold modalStepBranchGen
  refine stepBranch_findSome?_proj4to3 ?_ ?_ b newBs newExps newAcc keys' hstep
  · -- hpt: pointwise, the keyed inner computation projects to the generic one.
    intro sf a bb c k h
    split_ifs at h ⊢ with hexp
    rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
    rw [hpair] at h
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h; simp at h
  · -- hnone: pointwise, both drivers skip the same elements.
    intro sf h
    split_ifs at h ⊢ with hexp
    · rfl
    · rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
      rw [hpair] at h
      rcases hres : result with nf | brs | nf | -
      · rw [hres] at h; simp at h
      · rw [hres] at h; simp at h
      · rw [hres] at h; simp at h
      · rfl

omit [Hashable Atom] in
/-- **Local re-derivation** of `FmpMeasure.lean`'s `private modalExpMeasure_split`
(`:3174`), territory-local per Phase 3's own convention (`_S4` suffix) since the upstream
lemma is `private` and out of territory. Identical proof, universe-generic in `U`. -/
private lemma modalExpMeasure_split_S4
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
/-- **Local re-derivation** of `FmpMeasure.lean`'s `private modalExpMeasure_append`
(`:3191`), territory-local per Phase 3's own convention. Identical proof, universe-generic
in `U`. -/
private lemma modalExpMeasure_append_S4
    (U : List (SignedFormula (Proposition Atom) WorldIndex))
    (l1 l2 : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (e1 e2 : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (h : l1.length = e1.length) :
    modalExpMeasure U (l1 ++ l2) (e1 ++ e2)
      = modalExpMeasure U l1 e1 + modalExpMeasure U l2 e2 := by
  simp only [modalExpMeasure, List.zip_append h, List.map_append, List.sum_append]

end Cslib.Logic.Modal.Tableau

end
