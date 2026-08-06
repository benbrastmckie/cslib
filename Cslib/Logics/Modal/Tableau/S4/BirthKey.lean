/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.S4.Universe

/-! # S4 Loop-Checking: Birth-Content and Box-Plus Machinery

The birth-content computation (`successorBirthContent`) that predicts a fresh successor's
relevant formula set before it is minted, and the box-plus enrichment
(`boxPlusPair`/`BoxPlusClosed`/`boxPlusExtraS4`) that extends it with the box-context
transmitted from the minting world -- plus `keysOriginS4`, the per-key origin-edge bookkeeping
the keyed driver threads alongside it.

## Why a separate module

This module's declarations occupy **seven disjoint runs** in the original `LoopChecking.lean`,
interleaved between `Universe` (below) and `Guard`/`Driver` (above): birth-content and box-plus
are used immediately by the mint-shape guard and the driver's minting arms, but are themselves
built purely from `Universe`-layer facts (`signedSubfmls`, `relevantSetFinset`,
`sameRelevantSet`). Extracting them here makes that one-directional dependency explicit: this
module imports only `Universe`, and everything above it (`Guard`, `Driver`, ...) imports this.

## Main Definitions
- `successorBirthContent`: the prospective birth content of a fresh successor.
- `boxPlusPair`, `BoxPlusClosed`, `boxPlusExtraS4`: the box-plus enrichment machinery.
- `keysOriginS4`: per-key origin-edge bookkeeping threaded alongside the keyed driver.

## Main Results
- `boxPlusExtraS4_label_eq_freshWorld`, `relevantSetFinset_boxPlus_mono`: box-plus structural
  facts.
- `keysOriginS4_entry`, `keysOriginS4_mono_branch`, `keysOriginS4_mono_acc`: `keysOriginS4`
  characterization and monotonicity.
- `boxPlusExtraS4_outputs_subset_S4`, `boxPlus_pos_disjunct_elim`, `boxPlus_neg_disjunct_elim`,
  `successorBirthContent_boxPlusClosed`, `successorBirthContent_subset_signedSubfmls`: the
  universe-membership and closure facts `keyLowerBd` (`S4/InvariantKeys.lean`) consumes.

**Not here**: `successorBirthContent_boxNeg_subset_relevantSetFinset` and
`successorBirthContent_diamondPos_subset_relevantSetFinset`, despite their `successorBirthContent`
name prefix, live in `S4/InvariantKeys.lean` -- they reference `modalApplyOneS4KeyedMint` and its
equation lemmas, which are `Driver`-layer, so keeping them here would create a forward edge.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- The prospective birth content of the successor that would be minted for the modal-minting
call at `⟨s, φ, w⟩` (the two K minting shapes `F(□φ)@w`/`T(◇φ)@w`, `s` the witness's sign) at
branch `b`: the witness signed pair `(s, φ)` together with the S4 box-context transmitted from
`w` -- `(Sign.pos, ψ)` for every `T(□ψ)@w ∈ b` and `(Sign.neg, ψ)` for every `F(◇ψ)@w ∈ b`,
PLUS the box-plus members: `(Sign.pos, □ψ)` for every `T(□(□ψ))@w ∈ b` and `(Sign.neg, ◇ψ)` for
every `F(◇(◇ψ))@w ∈ b` -- i.e. every `p ∈ signedSubfmls φ₀` that is ITSELF a box-plus image
(`boxPlusPair`'s codomain shape, `.box _`/`.diamond _` on the appropriate sign) whose own
box-plus partner is transmitted from `w`. The first two disjuncts are kept FIRST and
syntactically VERBATIM (several proofs pattern-match their exact shape); the box-plus
enrichment is appended as two new disjuncts, using a `match`-on-`p.2` form so the predicate
stays decidable without an existential (`boxPlusPair` documents the same relationship the
existing two disjuncts already express, reformulated). Matches the actual K-minting birth
content (`modalApplyOne`'s `boxNeg`/`diamondPos` arms, `Rules.lean`, now additively enriched by
`modalApplyOneS4KeyedMint`/`boxPlusExtraS4`), restricted to `signedSubfmls φ₀`-relevant pairs.
Computed entirely from data already on `b` at mint time; stable (never recomputed once the
world is born) -- this is exactly the property that makes `S4LoopInv.keyLowerBd` (below) a
genuine loop invariant where the old `worldSetsDistinct` (over the live branch) was not
(Gap 1). -/
def successorBirthContent (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) : Finset (Sign × Proposition Atom) :=
  insert (s, φ) ((signedSubfmls φ₀).filter (fun p =>
    -- unchanged, kept first and verbatim:
    (p.1 = Sign.pos ∧
      b.any (· == (⟨.pos, .box p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex))) ∨
    (p.1 = Sign.neg ∧
      b.any (· == (⟨.neg, .diamond p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex))) ∨
    -- box-plus members, appended:
    (p.1 = Sign.pos ∧ (match p.2 with
      | .box _ => b.any (· == (⟨.pos, p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
      | _ => false) = true) ∨
    (p.1 = Sign.neg ∧ (match p.2 with
      | .diamond _ => b.any (· == (⟨.neg, p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
      | _ => false) = true)))

/-- The box-plus partner of a signed pair: `(pos, ψ) ↦ (pos, □ψ)`, `(neg, ψ) ↦ (neg, ◇ψ)`. The
**existing** `successorBirthContent` filter is already exactly "`boxPlusPair p` instantiated at
`w` is on `b`" -- this definition names that relationship. The box-plus enrichment of
`successorBirthContent` additionally records `p` itself whenever `p` is already a box-plus
IMAGE present on the branch (i.e. whenever `boxPlusPair`'s own output, instantiated at `w`, is
on `b` -- the case `p` itself is `.box _`/`.diamond _`-shaped). -/
def boxPlusPair (p : Sign × Proposition Atom) : Sign × Proposition Atom :=
  match p.1 with
  | .pos => (.pos, .box p.2)
  | .neg => (.neg, .diamond p.2)

/-- **Box-plus closure, scoped to the transmitted box-context filter** (report §5.2) --
NEVER a closure property of the whole key `k`: the witness pair enters `k` by `insert` and
satisfies neither closure direction (a mint from `F(□(□χ))@w` has witness `(neg, □χ)`, and
neither `(neg, χ)` nor `(neg, ◇□χ)` need be on the branch at birth). For every `p ∈ signedSubfmls
φ₀` whose box-plus partner `boxPlusPair p` is transmitted from `w` (i.e. `boxPlusPair p`
instantiated at `w` is on `b`), `k` records BOTH `p` itself and (when still within `Σ`) its own
box-plus partner `boxPlusPair p`. `successorBirthContent_boxPlusClosed` below shows every birth
key satisfies this by construction; threaded as a derived extra hypothesis where needed, never
an `S4LoopInv`/`S4KeyedHintikkaInv` field (the same treatment `keysOriginS4` receives, and
`keysRootEmpty` received before it was archived at
`Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean`). -/
def BoxPlusClosed (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) (k : Finset (Sign × Proposition Atom)) : Prop :=
  ∀ p ∈ signedSubfmls φ₀,
    (⟨(boxPlusPair p).1, (boxPlusPair p).2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
      p ∈ k ∧ (boxPlusPair p ∈ signedSubfmls φ₀ → boxPlusPair p ∈ k)

/-- The additive box-plus mint extra: the BOXED members `T(□ψ)@w'`/`F(◇ψ)@w'` for every
`T(□ψ)@w`/`F(◇ψ)@w` on the branch, retargeted to the freshly-minted successor
`w' = modalNextWorld b` -- alongside (never in place of) the UNWRAPPED members `modalApplyOne`'s
own payload already transmits. The two halves mirror `modalApplyOne`'s own `boxProps`/
`diaNegProps` halves verbatim, boxing the transmitted formula instead of leaving it unwrapped.
Keeps the same per-formula dedup guard (`if b.any (· == sf') then none else some sf'`) as
`modalApplyOne`'s own halves -- the freshness half of `modalApplyOneS4Keyed_persistentFresh_S4`
and the measure argument both key off this guard. -/
def boxPlusExtraS4 (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let w' := modalNextWorld b
  (boxPositivesOf b).filterMap (fun (ψ, src) =>
    if src == w then
      let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, .box ψ, w'⟩
      if b.any (· == sf') then none else some sf'
    else none) ++
  b.filterMap (fun sf' =>
    if sf'.sign == .neg && sf'.label == w then
      match sf'.formula with
      | .diamond ψ =>
        let pr : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, .diamond ψ, w'⟩
        if b.any (· == pr) then none else some pr
      | _ => none
    else none)

omit [Hashable Atom] in
/-- Every `boxPlusExtraS4` element's label is exactly `modalNextWorld b`, by construction --
both halves are built entirely at the one fresh label `w'`. Dual of
`FmpMeasure.lean`'s `mintGroup_label_eq_freshWorld` for the box-plus extra alone; combined with
that lemma at each mint call site via `List.mem_append`, since the actual keyed payload is
`modalApplyOne`'s own group ++ `boxPlusExtraS4`. -/
lemma boxPlusExtraS4_label_eq_freshWorld
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex) :
    ∀ x ∈ boxPlusExtraS4 b w, x.label = modalNextWorld b := by
  intro x hx
  simp only [boxPlusExtraS4, List.mem_append, List.mem_filterMap] at hx
  rcases hx with hx | hx
  · obtain ⟨⟨ψ, src⟩, -, heq⟩ := hx
    split at heq
    · split at heq
      · simp at heq
      · simp only [Option.some.injEq] at heq; subst heq; rfl
    · simp at heq
  · obtain ⟨sf', -, heq⟩ := hx
    split at heq
    · split at heq
      · rename_i ψ hform
        split at heq
        · simp at heq
        · simp only [Option.some.injEq] at heq; subst heq; rfl
      · simp at heq
    · simp at heq

omit [Hashable Atom] in
/-- **Payload-growth bridge for `relevantSetFinset`.** Whatever `successorBirthContent_boxNeg_
subset_relevantSetFinset`/`_diamondPos_subset_relevantSetFinset` prove against `modalApplyOne`'s
own (unwrapped-only, smaller) payload continues to hold against the additive keyed mint's
(box-plus-enriched, larger) payload: `relevantSetFinset` is monotone in the branch
(`relevantSetFinset_mono`), and every element of `oldForms ++ b` is trivially an element of
`(oldForms ++ boxPlusExtraS4 b w) ++ b`. -/
lemma relevantSetFinset_boxPlus_mono (φ₀ : Proposition Atom)
    (b oldForms : List (SignedFormula (Proposition Atom) WorldIndex)) (w w' : WorldIndex) :
    relevantSetFinset φ₀ (oldForms ++ b) w' ⊆
      relevantSetFinset φ₀ ((oldForms ++ boxPlusExtraS4 b w) ++ b) w' := by
  apply relevantSetFinset_mono
  intro x hx
  simp only [List.mem_append] at hx ⊢
  tauto

/-- **The origin-edge invariant.** Every non-root recorded key `(w, k) ∈ keys` has an origin
mint source `u` with an edge `u → w` already in `acc`, and every signed pair in `k` is either
that mint's own witness pair `(s', φ')`, or is *currently* present at `u` in its box/diamond
form, OR (box-plus enrichment) is itself box/diamond-shaped and its ONE-LESS-BOXED partner is
*currently* present at `u` in box/diamond form -- the third disjunct is exactly
`successorBirthContent`'s third/fourth filter disjunct (`boxPlus_pos_disjunct_elim`/
`boxPlus_neg_disjunct_elim`'s conclusion), needed because a box-plus member `(pos, □χ) ∈ k`
comes from `T(□χ)@u ∈ b` (one box), never from the doubly-boxed `T(□(□χ))@u ∈ b` the ORIGINAL
two-disjunct form would demand. `(s', φ')` is existentially bound once per key (a key has
exactly one witness pair, per `successorBirthContent`'s `insert (s, φ) (...)` shape). Stated
over the current `b`/`acc` (see module docstring above for why), so
`keysOriginS4_mono_branch`/`keysOriginS4_mono_acc` below are immediate -- the third disjunct is
STILL a plain `∈ b` membership fact (just guarded by an existential decomposition of `ψ`), so it
transports under branch growth exactly like the second.

**No `φ₀` parameter** (deviation from the plan's proposed shape, forced by `lake lint`'s
`unusedArguments` linter: unlike `S4LoopInv`'s fields, this invariant's statement never needs the
fixed-formula universe `φ₀` at all). Mirrors `worldsContiguousS4` (above), the other
proof-internal auxiliary that also takes no `φ₀`.

**Not the abandoned `keysOriginS4`-strengthening route.** The "Redirect-Inertness Assembly --
REMOVED" section below warns against strengthening `keysOriginS4` to try to rescue
`blockedRedirect_boxctx_mem`, a DIFFERENT, since-removed lemma whose conclusion was machine-
checked FALSE. This third disjunct is a different, narrower change: a permissive weakening of
`keysOriginS4`'s own conclusion, needed only because the birth key itself now records box-plus
members, not an attempt to force a false conclusion true. The box-plus payoff lemmas
(`blockedRedirect_boxed_boxPos_mem`/`_diaNeg_mem`) are derived directly from `keyLowerBd`, per
that section's own recommended repair, and do not consume `keysOriginS4` at all. -/
def keysOriginS4
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop :=
  ∀ w k, (w, k) ∈ keys → w = 0 ∨
    ∃ u s' φ', acc.hasEdge u w = true ∧
      (∀ ψ, (Sign.pos, ψ) ∈ k →
         (s', φ') = ((Sign.pos, ψ) : Sign × Proposition Atom) ∨
         (⟨.pos, .box ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ∨
         (∃ χ, ψ = .box χ ∧
           (⟨.pos, .box χ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)) ∧
      (∀ ψ, (Sign.neg, ψ) ∈ k →
         (s', φ') = ((Sign.neg, ψ) : Sign × Proposition Atom) ∨
         (⟨.neg, .diamond ψ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ∨
         (∃ χ, ψ = .diamond χ ∧
           (⟨.neg, .diamond χ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b))

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Entry establishment**: `keysOriginS4` holds at the ordered driver's seed state. The sole
recorded key is `(0, ∅)` (`modalTableauS4KeyedOrdered`'s seed), so the only membership case is
`w = 0`, the invariant's root disjunct, discharged immediately. -/
lemma keysOriginS4_entry (φ : Proposition Atom) :
    keysOriginS4
      ([⟨.neg, φ, 0⟩] : List (SignedFormula (Proposition Atom) WorldIndex))
      Accessibility.empty
      [(0, (∅ : Finset (Sign × Proposition Atom)))] := by
  intro w k hmem
  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
  exact Or.inl hmem.1

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Survives branch growth**: `keysOriginS4` transports across `b ⊆ b'` at fixed `acc`/`keys`.
Every disjunct in the invariant is either branch-independent (the edge conjunct, the root case)
or an `∈ b` membership fact, which persists under `hsub`. -/
lemma keysOriginS4_mono_branch
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hsub : ∀ x ∈ b, x ∈ b') (h : keysOriginS4 b acc keys) :
    keysOriginS4 b' acc keys := by
  intro w k hmem
  rcases h w k hmem with hroot | ⟨u, s', φ', hedge, hpos, hneg⟩
  · exact Or.inl hroot
  · refine Or.inr ⟨u, s', φ', hedge, ?_, ?_⟩
    · intro ψ hψ
      rcases hpos ψ hψ with heq | hbox | ⟨χ, hχ, hbox⟩
      · exact Or.inl heq
      · exact Or.inr (Or.inl (hsub _ hbox))
      · exact Or.inr (Or.inr ⟨χ, hχ, hsub _ hbox⟩)
    · intro ψ hψ
      rcases hneg ψ hψ with heq | hdia | ⟨χ, hχ, hdia⟩
      · exact Or.inl heq
      · exact Or.inr (Or.inl (hsub _ hdia))
      · exact Or.inr (Or.inr ⟨χ, hχ, hsub _ hdia⟩)

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Survives edge addition**: `keysOriginS4` transports across accessibility growth (every
edge of `acc` also an edge of `acc'`) at fixed `b`/`keys`. `keysOriginS4` is existential over
edges, so this is immediate. -/
lemma keysOriginS4_mono_acc
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc acc' : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (haccsub : ∀ u w, acc.hasEdge u w = true → acc'.hasEdge u w = true)
    (h : keysOriginS4 b acc keys) :
    keysOriginS4 b acc' keys := by
  intro w k hmem
  rcases h w k hmem with hroot | ⟨u, s', φ', hedge, hpos, hneg⟩
  · exact Or.inl hroot
  · exact Or.inr ⟨u, s', φ', haccsub u w hedge, hpos, hneg⟩

/-! ### Case-(b) Conditional Derivation

The load-bearing half of the redirect-inertness argument, proved standalone here so
it lands regardless of how the witness gate below resolves: given an ALREADY-EXISTING edge
`u → wBlock` and `T(□ψ)@u ∈ b`, mint-readiness forces `T(□ψ)@wBlock ∈ b` -- otherwise
`modalFourBoxProp` at `(u, wBlock)` would still be an unsettled non-mint candidate, contradicting
`modalNonMintCandidates φ₀ keys b e acc = []`. Symmetric statement for `modalFourDiaNegProp`. -/

omit [Hashable Atom] in
/-- Closure fact for `boxPlusExtraS4`'s box-positive half: unlike `boxProps_outputs_subset_S4`,
the transmitted formula is `.box ψ` ITSELF, already a member of `modalSubfmls φ₀` by the
membership hypothesis directly -- no `modalSubfmls_trans` needed, since `.box ψ` is not being
further unwrapped. -/
private lemma boxPlusExtraS4_boxHalf_outputs_subset_S4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀) :
    ∀ x ∈ (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex :=
            ⟨.pos, .box ψ, modalNextWorld b⟩
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
      exact mem_modalUniverseS4_of hwbound hψsub
  · simp at heq

omit [Hashable Atom] in
/-- Dual of `boxPlusExtraS4_boxHalf_outputs_subset_S4` for `boxPlusExtraS4`'s diamond-negative
half. -/
private lemma boxPlusExtraS4_diaHalf_outputs_subset_S4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀) :
    ∀ x ∈ b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .diamond ψ =>
            let pr : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, .diamond ψ, modalNextWorld b⟩
            if b.any (· == pr) then none else some pr
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
        exact mem_modalUniverseS4_of hwbound hψsub
    · simp at heq
  · simp at heq

omit [Hashable Atom] in
/-- `boxPlusExtraS4`'s output stays inside `U_{S4}(φ₀)`, combining both halves above. Consumed
by the extended `modalApplyOne_boxNeg_outputs_subset_S4`/`_diamondPos_outputs_subset_S4` below. -/
lemma boxPlusExtraS4_outputs_subset_S4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hwbound : modalNextWorld b ≤ modalWorldBoundS4 φ₀) :
    ∀ x ∈ boxPlusExtraS4 b w, x ∈ modalUniverseS4 φ₀ := by
  intro x hx
  simp only [boxPlusExtraS4, List.mem_append] at hx
  rcases hx with hx | hx
  · exact boxPlusExtraS4_boxHalf_outputs_subset_S4 φ₀ b w hb hwbound x hx
  · exact boxPlusExtraS4_diaHalf_outputs_subset_S4 φ₀ b w hb hwbound x hx

omit [Hashable Atom] in
/-- Elimination form for `successorBirthContent`'s third (box-plus positive) disjunct: if the
`match`-guarded predicate holds for `p2`, then `p2` is necessarily `.box ψ` for some `ψ`, and
the UNWRAPPED box-positive `T(□ψ)@w` is on the branch. The other six `Proposition` shapes make
the match reduce to `false = true`, discharged by contradiction. -/
lemma boxPlus_pos_disjunct_elim {p2 : Proposition Atom} {w : WorldIndex}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hpb : (match p2 with
        | .box _ => b.any (· == (⟨.pos, p2, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
        | _ => false) = true) :
    ∃ ψ, p2 = .box ψ ∧
      (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  rcases p2 with _ | _ | _ | _ | _ | ψ | ψ
  · simp at hpb
  · simp at hpb
  · simp at hpb
  · simp at hpb
  · simp at hpb
  · exact ⟨ψ, rfl, mem_of_any_beq_S4 hpb⟩
  · simp at hpb

omit [Hashable Atom] in
/-- Dual of `boxPlus_pos_disjunct_elim` for `successorBirthContent`'s fourth (box-plus
negative) disjunct. -/
lemma boxPlus_neg_disjunct_elim {p2 : Proposition Atom} {w : WorldIndex}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hpb : (match p2 with
        | .diamond _ =>
            b.any (· == (⟨.neg, p2, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
        | _ => false) = true) :
    ∃ ψ, p2 = .diamond ψ ∧
      (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  rcases p2 with _ | _ | _ | _ | _ | ψ | ψ
  · simp at hpb
  · simp at hpb
  · simp at hpb
  · simp at hpb
  · simp at hpb
  · simp at hpb
  · exact ⟨ψ, rfl, mem_of_any_beq_S4 hpb⟩

omit [Hashable Atom] in
/-- **`successorBirthContent` satisfies `BoxPlusClosed`, by construction.** Both conjuncts land
in the enriched filter's four disjuncts directly: `p ∈ k` via the ORIGINAL (unwrapped)
disjunct 1/2 -- since `boxPlusPair p` transmitted at `w` IS literally disjunct 1/2's own
condition on `p` -- and `boxPlusPair p ∈ k` (when in `Σ`) via the box-plus disjunct 3/4, whose
match-guarded condition on `boxPlusPair p` reduces to the SAME branch fact. No new proof content
beyond `successorBirthContent`'s own definition. -/
lemma successorBirthContent_boxPlusClosed (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) :
    BoxPlusClosed φ₀ b w (successorBirthContent φ₀ b s φ w) := by
  intro p hpmem hbp
  rcases hp1 : p.1 with _ | _
  · simp only [boxPlusPair, hp1] at hbp
    refine ⟨?_, ?_⟩
    · unfold successorBirthContent
      refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_filter]
      exact ⟨hpmem, Or.inl ⟨hp1, any_beq_of_mem_S4 hbp⟩⟩
    · intro hqmem
      unfold successorBirthContent
      refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_filter]
      simp only [boxPlusPair, hp1] at hqmem ⊢
      exact ⟨hqmem, Or.inr (Or.inr (Or.inl ⟨trivial, any_beq_of_mem_S4 hbp⟩))⟩
  · simp only [boxPlusPair, hp1] at hbp
    refine ⟨?_, ?_⟩
    · unfold successorBirthContent
      refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_filter]
      exact ⟨hpmem, Or.inr (Or.inl ⟨hp1, any_beq_of_mem_S4 hbp⟩)⟩
    · intro hqmem
      unfold successorBirthContent
      refine Finset.mem_insert_of_mem ?_
      rw [Finset.mem_filter]
      simp only [boxPlusPair, hp1] at hqmem ⊢
      exact ⟨hqmem, Or.inr (Or.inr (Or.inr ⟨trivial, any_beq_of_mem_S4 hbp⟩))⟩

/-! ### `keysOriginS4` Consumer Audit -- Retraction of an Earlier Hedge

**Consumer audit (measured; supersedes an earlier hedge).** An earlier revision of this comment
(then filed under a now-archived `### keysRootEmpty` heading -- `keysRootEmpty` and
`keysRootEmpty_entry` are archived at `Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean`, whose
README carries the travelled consumer-audit paragraphs for that fact) stated that a since-removed
lemma's sole consumer `blockedRedirect_boxctx_mem` was removed "along with `keysOriginS4` and its
supporting lemmas", and marked the archived `keysRootEmpty` fact itself "possibly orphaned". Both
halves are corrected here against a measured consumer audit. Only
`blockedRedirect_boxctx_mem`/`blockedRedirect_diaNeg_mem` were in fact removed (they were false as
stated -- see the "Redirect-Inertness Assembly" section below).

`keysOriginS4` was **not** removed and is **not** orphaned. It is still declared in this file
(`keysOriginS4`, together with `keysOriginS4_entry`, `keysOriginS4_mono_branch` and
`keysOriginS4_mono_acc`) and is referenced pervasively:

```
grep -rn 'keysOriginS4' --include='*.lean' Cslib/ | wc -l
grep -rn 'keysOriginS4' --include='*.lean' Cslib/ \
  | grep -vE ':[[:space:]]*(--|[/][-]|[-][|]|[*])' | wc -l
```

61 textual references, 55 of them on lines that do not begin with a comment marker, all inside
this file. Any future claim that `keysOriginS4` was deleted is false and should not be
reintroduced. -/

/-! ### Redirect-Inertness Assembly -- REMOVED

`blockedRedirect_boxctx_mem` and `blockedRedirect_diaNeg_mem` were removed here: both were
**FALSE as stated**, not merely unproven, so their `sorry`s were an unsound foundation rather
than a documented gap. Machine-checked in
`reports/02_redirect-inertness-divergence-audit.md` (§2.2): driving
`modalStepBranchS4KeyedOrdered` on `φ₀ = ¬(◇p ∧ ◇(□p ∧ ◇p))` from the seed state reaches a step
at which every hypothesis of `blockedRedirect_boxctx_mem` holds -- including `keysOriginS4`,
`keysRootEmpty` (now archived at `Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean`),
mint-readiness, and the guard's `some` output
(`blockingWorldS4Keyed φ₀ b keys .pos p 2 = some 1`, redirecting `2 → 1`) -- while its conclusion
`T(□p)@1 ∈ b` evaluates to `false`. `blockedRedirect_diaNeg_mem` fails by the symmetric
construction (argued in the report, not independently machine-checked). Do not re-attempt either
statement as worded, and do not try to close the gap by strengthening `keysOriginS4`/adding a
guard side-condition: the audit's Question (3) shows both routes are dead ends (the former has no
target since the conclusion is false; the latter breaks `keysDistinct` and the pigeonhole world
bound). The report's recommended repair (recording box-context keys in *boxed* form) replaces
this argument outright with a three-line consequence of the already-landed
`S4LoopInv.keyLowerBd`. -/

omit [Hashable Atom] in
/-- Every `successorBirthContent` value lies in `signedSubfmls φ₀`, provided its witness
formula `φ` is a subformula of `φ₀`: the `insert (s, φ)` component needs
`mem_signedSubfmls_of_formula_S4`, and the filtered remainder is trivially a subset of
`signedSubfmls φ₀` (`Finset.filter_subset`). Reusable by both minting leaves of
`keysInUniverse`'s preservation (unlike the `relevantSetFinset`-targeted subset lemmas above,
this fact needs no information about the POST-step branch at all). -/
lemma successorBirthContent_subset_signedSubfmls
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex) (hφ : φ ∈ modalSubfmls φ₀) :
    successorBirthContent φ₀ b s φ w ⊆ signedSubfmls φ₀ := by
  intro p hp
  simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨hpmem, -⟩
  · exact mem_signedSubfmls_of_formula_S4 s hφ
  · exact hpmem


end Cslib.Logic.Modal.Tableau

end
