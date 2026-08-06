/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Dedup
public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.FrameRules

/-! # S4 Loop-Checking: Universe, Fuel, and Signed-Subformula Machinery

The lowest layer of the S4 loop-checking cluster: per-world relevant-formula-set extraction
(`formulasAtWorld`, `sameRelevantSet`), the world-bound/fuel measures that size the whole
S4 tableau search (`modalWorldBoundS4`, `modalUniverseS4`, `modalFuelS4`), and the
`signedSubfmls`/`relevantSetFinset` bookkeeping the minting guard and the loop invariant both
consult.

## Why a separate module

This module's declarations occupy **six disjoint runs** spanning what were lines 229-9499 of
the original `LoopChecking.lean` (L229-529, L1815-1857, L2323-2367, L6067-6084, L8124-8195,
L9480-9499) -- a reader who does not already know the dependency structure will find that
provenance arbitrary. It is not arbitrary: every declaration here is a leaf of the S4
dependency graph (imports nothing else in the `S4/` cluster), so each was free to be defined
wherever in the original file was locally convenient at the time, near whichever downstream
consumer needed it first. Extracting them into one module makes the leaf-layer status the
declarations' organizing principle explicit, rather than leaving it implicit in a dependency
graph a reader would have to reconstruct by hand.

## Main Definitions
- `formulasAtWorld`, `sameRelevantSet`: per-world formula-set extraction and equivalence.
- `modalWorldBoundS4`, `modalUniverseS4`, `modalFuelS4`: the world-bound and fuel measures
  that size the S4 tableau search.
- `signedSubfmls`, `relevantSetFinset`: the signed-subformula universe and its per-world
  relevance restriction.

## Main Results
- `sameRelevantSet_iff`, `_refl`, `_symm`, `_trans`: `sameRelevantSet` is an equivalence.
- `modalUniverseS4_length_le`, `signedSubfmls_card_le`, `signedSubfmls_powerset_card_le`,
  `relevantSetFinset_subset_signedSubfmls`, `relevantSetFinset_mono`: the cardinality and
  monotonicity facts the fuel/termination argument consumes.
- `mem_modalUniverseS4_of`, `mem_modalUniverseS4_of'`, `modalUniverseS4_mem_label`,
  `modalUniverseS4_mem_formula`: membership characterizations for `modalUniverseS4`.
- `any_beq_of_mem_S4`, `mem_of_any_beq_S4`: `List.any (· == ·)` bridges to plain membership.
  `modalNextWorld_fresh_beq_S4`, `mem_signedSubfmls_of_formula_S4`,
  `mem_signedSubfmls_of_formula_s4loop`: freshness and relevance-set membership facts the
  minting guard and the loop invariant both consult.
- `modalTBoxSelf_fresh`, `modalTDiaNegSelf_fresh`, `modalFourBoxProp_fresh`,
  `modalFourDiaNegProp_fresh`: freshness facts for the T-self and four-rule box/diamond shapes.
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

omit [DecidableEq Atom] [Hashable Atom] in
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

omit [DecidableEq Atom] [Hashable Atom] in
/-- Extraction: the formula-component of any `modalUniverseS4 φ₀` member is a subformula of
`φ₀`. S4-local restatement of `FmpMeasure.lean`'s file-private `modalUniverse_mem_formula`.
Made non-`private` (probe P1, `specs/553_s4_loop_guard_soundness_reachability_restriction/`) so
`FrameCompleteness.lean`'s reformulated redirect-sound invariant can re-derive the same
`signedSubfmls` relevance side condition `modalS4Saturated_addEdge_of_blocked` already
establishes locally in this file -- a pure visibility widening, no proof content changed. -/
lemma modalUniverseS4_mem_formula {φ₀ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverseS4 φ₀) :
    x.formula ∈ modalSubfmls φ₀ := by
  simp only [modalUniverseS4, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, -, ψ, hψ, heq | heq⟩ := hx <;> (subst heq; exact hψ)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Extraction: the label-component of any `modalUniverseS4 φ₀` member is bounded by
`modalWorldBoundS4 φ₀`. S4-local restatement of `FmpMeasure.lean`'s file-private
`modalUniverse_mem_label`. -/
lemma modalUniverseS4_mem_label {φ₀ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverseS4 φ₀) :
    x.label ≤ modalWorldBoundS4 φ₀ := by
  simp only [modalUniverseS4, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, ψ, -, heq | heq⟩ := hx <;> (subst heq; exact Nat.lt_succ_iff.mp hw)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Constructor direction for `modalUniverseS4` membership: a signed formula with any sign,
a subformula of `φ₀`, at a world label within the bound, is in `U_{S4}(φ₀)`. S4-local
restatement of `FmpMeasure.lean`'s file-private `mem_modalUniverse_of`. -/
lemma mem_modalUniverseS4_of {φ₀ : Proposition Atom} {s : Sign} {φ : Proposition Atom}
    {w : WorldIndex} (hw : w ≤ modalWorldBoundS4 φ₀) (hφ : φ ∈ modalSubfmls φ₀) :
    (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverseS4 φ₀ := by
  have hlt : w < modalWorldBoundS4 φ₀ + 1 := Nat.lt_succ_of_le hw
  simp only [modalUniverseS4, List.mem_flatMap, List.mem_range]
  exact ⟨w, hlt, φ, hφ, by cases s <;> simp⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Generic form of `mem_modalUniverseS4_of`, stated for an arbitrary signed formula `z` rather
than a literal anonymous constructor (needed by case-split proofs over already-opaque signed
formulas). S4-local restatement of `FmpMeasure.lean`'s file-private `mem_modalUniverse_of'`. -/
lemma mem_modalUniverseS4_of' {φ₀ : Proposition Atom}
    {z : SignedFormula (Proposition Atom) WorldIndex}
    (hw : z.label ≤ modalWorldBoundS4 φ₀) (hφ : z.formula ∈ modalSubfmls φ₀) :
    z ∈ modalUniverseS4 φ₀ := by
  obtain ⟨s, φ, w⟩ := z
  exact mem_modalUniverseS4_of hw hφ

omit [Hashable Atom] in
/-- If `t ∈ l`, then `l.any (· == t) = true`. Converts a `List.mem` fact into the `Bool`-valued
form `relevantSetFinset`/`successorBirthContent` filter on. -/
lemma any_beq_of_mem_S4 {l : List (SignedFormula (Proposition Atom) WorldIndex)}
    {t : SignedFormula (Proposition Atom) WorldIndex} (h : t ∈ l) : l.any (· == t) = true := by
  rw [List.any_eq_true]
  exact ⟨t, h, by simp⟩

omit [Hashable Atom] in
/-- Converse of `any_beq_of_mem_S4`: `l.any (· == t) = true` gives `t ∈ l`. -/
lemma mem_of_any_beq_S4 {l : List (SignedFormula (Proposition Atom) WorldIndex)}
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
lemma modalNextWorld_fresh_beq_S4
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
lemma mem_signedSubfmls_of_formula_S4 {φ₀ : Proposition Atom} (s : Sign)
    {ψ : Proposition Atom} (h : ψ ∈ modalSubfmls φ₀) : (s, ψ) ∈ signedSubfmls φ₀ := by
  simp only [signedSubfmls, Finset.mem_product, List.mem_toFinset]
  refine ⟨?_, h⟩
  cases s <;> simp

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

omit [Hashable Atom] in
/-- `modalTBoxSelf`'s nonempty branch is exactly `[sf]` with `sf ∉ b` by the guard itself. -/
lemma modalTBoxSelf_fresh
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
lemma modalTDiaNegSelf_fresh
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
lemma modalFourBoxProp_fresh
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
lemma modalFourDiaNegProp_fresh
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
/-- Bridge: a formula's membership in `modalSubfmls φ₀` extends to `signedSubfmls φ₀`
membership at either sign, since `signedSubfmls` is the full `{pos, neg} × modalSubfmls φ₀`
product. Local restatement of `S5Simplification.lean`'s file-private
`mem_signedSubfmls_of_formula_S5w`, needed here because `signedSubfmls` (unlike
`modalUniverseS4`) carries no world-label component to case on. -/
lemma mem_signedSubfmls_of_formula_s4loop {φ₀ : Proposition Atom} (s : Sign)
    {ψ : Proposition Atom} (h : ψ ∈ modalSubfmls φ₀) : (s, ψ) ∈ signedSubfmls φ₀ := by
  unfold signedSubfmls
  rw [Finset.mem_product]
  refine ⟨?_, List.mem_toFinset.mpr h⟩
  cases s <;> simp


end Cslib.Logic.Modal.Tableau

end
