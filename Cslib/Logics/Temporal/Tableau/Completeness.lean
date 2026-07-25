/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Temporal.Tableau.Soundness
public import Mathlib.Algebra.Order.ToIntervalMod

/-! # Temporal Tableau Completeness

This module provides the completeness side of the temporal tableau decision
procedure: an open saturated branch yields a countermodel.

## Main Results (Proved)

- `extractModel`: Constructs a `TemporalModel Nat Atom` from a branch; atoms are
  satisfied iff T(atom p)@t appears on the branch.
- `extractModel_atom_sat_iff`: Atom satisfaction in `extractModel b` is determined
  by the presence of T(atom p)@t on the branch.
- `extractModel_bot_false`: ⊥ is never satisfied in any extracted model.
- `openBranch_noBotPos`: An open branch has no T(⊥) on it.
- `openBranch_noContradiction`: An open branch has no simultaneous T(φ)@t and F(φ)@t.
- `extractModel_atom_neg_notSat`: F(atom p)@t on an open branch implies
  ¬ Satisfies (extractModel b) t (.atom p).
- `extractModelℤ`: Constructs a `TemporalModel ℤ Atom` keyed on `ord.instant`, the
  countermodel underlying `openBranch_branchSat`: the time domain is `D = ℤ` with
  `f = ord.instant`, which is order-preserving by `InstantStrict`.
- `extractModelℤ_atomPos_sat`, `extractModelℤ_bot_false`: Basic properties of the ℤ model.
- `extractModelℤ_atom_neg_notSat`: Negative atom property (requires injectivity hypothesis).
- `periodicReduce` / `periodicReduce_mem_Ico_of_gt`, `extractModelℤPeriodic` + its three
  property lemmas: the forward (future-tail) half of the bi-lasso periodic countermodel spike
  (plan round 04, Phase 4), parameterized by an explicit loop witness `(instAnc, instNew)`.
- `periodicReducePast` / `periodicReducePast_mem_Ico_of_lt`, `extractModelℤPeriodicPast` + its
  three property lemmas (Phase 4b): the symmetric backward (past-tail) half, completing the
  bi-lasso reduction machinery in both directions.
- `instantStrict_constraint_lt` (Phase 4a, partial): converts a recorded ordering-constraint
  edge `(t_anc, t_new) ∈ ord.constraints` plus `InstantStrict ord` into the `hL : ord.instant
  t_anc < ord.instant t_new` fact the periodic reductions need. This is the *conversion* half of
  Phase 4a; the *existence* half (deriving such an edge from a genuine `isSubsetBlocked`
  witness, for an arbitrary branch returned by `temporalTableau`) is the open gap documented
  below.

## Blocked Obligations

The following results cannot be proved in the current scope.

### Ordering Design

`TimeOrdering.InstantStrict` and the `D = ℤ / f = ord.instant` choice give the countermodel
its order structure; the `openBranch_branchSat` sketch below reflects this design. The run-level
`InstantStrict` proof is landed (`temporalTableau_instantStrict`, `Saturation.lean`); the
remaining blocker is the FMP construction for the Until/Since cases (below).

### Blocked (Proof Complexity — No Theoretical Blocker)

1. `temporalTruthLemma_propositional` (imp case): **Landed** (see Main Results above;
   `temporalTruthLemma_propositional_aux`/`temporalTruthLemma_propositional`).

### Blocked (FMP Existence Argument — Genuine Structural Gap, Not Merely Proof Complexity)

Plan round 04 (Phase 4c/4d) called for deriving the loop witness `(t_anc, t_new)` generically
from "a genuine `isSubsetBlocked` witness" produced by an arbitrary `temporalTableau φ =
.openBranch b ord` result, then wiring `extractModelℤPeriodic` in as the real `extractModelℤ`
and re-proving the FMP truth lemma (Phases 5-6) and completeness assembly (Phase 7) against it.
Careful tracing of `temporalStepBranch`/`processNext`/`isTemporalClosed`/`findEventualityDefect`
(`Saturation.lean`, `Closure.lean`, `Branch.lean`) found this premise does not hold generically,
for two compounding reasons:

2. **Genuinely-saturated open branches never need the loop.** `isTemporalClosed` (hence
   eventuality-defect closure via `findBlockedTime`/`isSubsetBlocked`) is re-checked at *every*
   worklist step, not only at the end. So if a branch's accumulated content ever satisfies
   `isSubsetBlocked b t t_anc` for a known ancestor with a genuinely pending eventuality, the
   branch closes *immediately* at that step — it can never survive to be returned open with that
   witness intact. Conversely, `temporalStepBranch b e ord tracker = none` (genuine saturation)
   requires every live Until/Since copy to have already resolved (`EventualityTracker.pending`
   empty), since an unresolved copy would still be expandable. So a genuinely-saturated open
   branch always has an *empty* tracker, for which the plain "island" `extractModel`/`extractModelℤ`
   already suffices (no unfulfilled eventuality ever needs a witness beyond the finite branch).
   The periodic bi-lasso construction is therefore only relevant for the *other* source of
   `.openBranch` results:
3. **Fuel-exhausted open branches (`temporalExpandBranches`'s `fuel = 0` case) may carry no
   internal loop witness at all.** This path returns the first branch with `isTemporalClosed =
   false`, regardless of whether `temporalStepBranch` would still find work to do. Because the
   same `isTemporalClosed` check (hence the same non-existence of any currently-blocked ancestor)
   applies here too, a fuel-exhausted branch with nonempty pending eventualities can be one that
   is *never actually looped* in the technical `isSubsetBlocked` sense at the moment fuel ran
   out — it is simply mid-expansion, cut off before any repeat had a chance to form. Deriving a
   genuine loop witness for *this* case requires an independent **fuel-sufficiency /
   pigeonhole theorem**: that `temporalFuel`'s bound (`Saturation.lean:76`, based on
   `2^(subformulaCount φ)` distinct time-types) is large enough that `isSubsetBlocked` *must*
   already hold among the branch's created labels whenever fuel exhausts with pending
   eventualities still open. This theorem is not yet formalized anywhere in the codebase; it is
   the actual mathematical content of the tableau's termination argument (report
   01 §3/§8.3's informal "the number of distinct time types is bounded by `2^n`" claim), and is
   independent from (and a prerequisite to) the periodic-model *definition* work landed in Phase
   4a/4b above.

   A secondary, narrower observation on the same theme, **now resolved**: `temporalStepBranch`'s
   `.branching` case (which `untlPos`/`sncePos`/`untlNeg`/`snceNeg`/all propositional branching
   rules use) used to pass `tracker` through **unchanged** — `registerEventualities`/
   `fulfillEventualities` were only called from the `.linear`/`.persistent` arms, so a positive
   Until/Since formula's *primary* recurring copy (`untlPos`'s `branch2`, `Rules.lean:271`) was
   never itself registered into `EventualityTracker.pending` by that call site. This is fixed:
   `temporalStepBranch` now returns one tracker **per output branch** (`Saturation.lean`'s
   `temporalStepBranch`/`temporalStepBranch_preserves_faithful`/`WorklistInvFaithful`), with each
   branch running its own `registerEventualities`/`fulfillEventualities` pass over exactly that
   branch's new formulas — so `untlPos`'s `branch1` (which fulfils the eventuality) and `branch2`
   (which defers it) now genuinely diverge in their pending sets, as they must. This narrows, but
   does not by itself close, the gap in (3): the fuel-sufficiency/pigeonhole theorem itself
   (bounding how long a genuinely-pending eventuality can survive before `isSubsetBlocked` must
   fire) remains unformalized; what changes is that `tracker.hasPending` now correctly reflects
   the "some Until copy is still live" fact for branching-rule outputs, removing what was
   previously an *additional*, independent source of unsoundness in that fact on top of the
   pigeonhole gap itself.

4. `temporalTruthLemma_untl`, `temporalTruthLemma_snce`: blocked by (2)/(3) — the periodic model
   these consume is not yet wired in generically, pending the fuel-sufficiency theorem.

5. `openBranch_branchSat`, `temporalTableau_complete`: blocked by (4).

## Remaining Work

1. ~~Complete the propositional truth lemma (imp case).~~ **Done.**
2. ~~Factor out `processNext` to enable loop invariant induction (unblocks the run-level
   `InstantStrict` proof).~~ **Done** (`temporalTableau_instantStrict`, `Saturation.lean`).
2a. ~~Extend `EventualityTracker` registration to cover `.branching` outputs
    (`untlPos`/`sncePos`/`untlNeg`/`snceNeg`).~~ **Done**: `temporalStepBranch` now returns a
    per-output-branch tracker list, each independently registered/fulfilled
    (`Saturation.lean`'s `temporalStepBranch`/`temporalStepBranch_preserves_faithful`).
3. Prove the fuel-sufficiency/pigeonhole theorem documented above (item 3 in "Blocked
   Obligations"): that `temporalFuel` guarantees `isSubsetBlocked` holds among a fuel-exhausted
   branch's own labels whenever pending eventualities remain. This is the prerequisite for
   wiring `extractModelℤPeriodic`/`periodicReducePast` in as the real `extractModelℤ` (Phase 4c)
   and completing Phases 5-7 (`temporalTruthLemma_untl`/`_snce`, `openBranch_branchSat`,
   `temporalTableau_complete`). Recommend a dedicated research pass before further planning; see
   `specs/425_temporal_tableau_ptl_fmp_decidability/` Phase 4 `[PARTIAL]` writeup for the
   complete trace.

## References

* [R. Reynolds, *An axiomatization of prior's tense logic*][Reynolds1994]
* [R. Smullyan, *First-Order Logic*][Smullyan1968] (propositional truth lemma pattern)
* Propositional Classical Completeness.lean (proof template)
* [I. Hodkinson and M. Reynolds, *Temporal Logic*][HodkinsonReynolds2006] (Handbook of Modal
  Logic, ch. 11, §5.8: the bidirectional ultimately-periodic bi-lasso ℤ-model construction
  underlying `extractModelℤ`)
* [C. Caleiro, L. Viganò, and M. Volpe, *On the Mosaic Method for Many-Dimensional Modal
  Logics*][CaleiroViganoVolpe2013] (§4.3: the mosaic-decidability route for `valid`, surveyed
  and rejected as non-transferable to the discrete case decided here)
* [D. Gabbay, I. Hodkinson, and M. Reynolds, *Temporal Expressive Completeness in the Presence
  of Gaps*][Gabbay1993]
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Temporal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Countermodel Extraction -/

/-- Extract a `TemporalModel Nat Atom` from an open branch.

The time domain is `Nat` (already a linear order). The valuation maps atom `p`
at time `t` to `true` iff T(atom p)@t appears on the branch.

When the branch is open and saturated (a Hintikka set), every formula on
the branch should be satisfied in this model. Proving this in full (the temporal
truth lemma) requires additional theory for the Until/Since cases; see the
module docstring. -/
def extractModel (b : TBranch Atom) : TemporalModel Nat Atom where
  valuation t p := b.any fun sf =>
    sf.sign == .pos && sf.label == t && sf.formula == .atom p

/-! ## Basic Model Properties -/

omit [Hashable Atom] in
/-- Atom satisfaction in `extractModel b` is equivalent to T(atom p)@t being on the branch. -/
lemma extractModel_atom_sat_iff (b : TBranch Atom) (t : TimeIndex) (p : Atom) :
    Satisfies (extractModel b) t (.atom p) ↔
    b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == .atom p) := by
  simp only [Satisfies.atom_iff, extractModel]

omit [Hashable Atom] in
/-- T(atom p)@t on a branch implies atom p is satisfied in the extracted model at t. -/
lemma extractModel_atomPos_sat (b : TBranch Atom) (t : TimeIndex) (p : Atom)
    (hmem : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b) :
    Satisfies (extractModel b) t (.atom p) := by
  rw [extractModel_atom_sat_iff, List.any_eq_true]
  exact ⟨⟨.pos, .atom p, t⟩, hmem, by simp⟩

omit [Hashable Atom] in
/-- ⊥ is never satisfied in any extracted model, at any time. -/
lemma extractModel_bot_false (b : TBranch Atom) (t : TimeIndex) :
    ¬ Satisfies (extractModel b) t .bot :=
  Satisfies.bot_false (extractModel b) t

/-! ## ℤ-Keyed Countermodel Extraction -/

/-- Extract a `TemporalModel ℤ Atom` from an open branch, keyed on the integer instant
assigned to each time label by the time ordering.

This is the corrected countermodel for `branchSat`: it uses the domain `D = ℤ` and the
order-preserving assignment `f = ord.instant`, supplying a time domain with a genuine
`LinearOrder` and `Nontrivial` instance. The valuation maps atom `p` at instant `z` to
`true` iff some signed formula T(atom p) at a time label with `ord.instant label = z`
appears on the branch.

Note: `ord.instant` may be non-injective (two labels can share an instant), making this
model well-defined but potentially "collapsing" distinct time points. For the positive atom
and ⊥ properties, non-injectivity poses no issue; the negative atom property requires
an additional injectivity hypothesis (see `extractModelℤ_atom_neg_notSat`). -/
def extractModelℤ (b : TBranch Atom) (ord : TimeOrdering) : TemporalModel ℤ Atom where
  valuation z p := b.any fun sf =>
    sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p

omit [Hashable Atom] in
/-- Atom satisfaction in `extractModelℤ b ord` is equivalent to there being some
T(atom p)@t on the branch with `ord.instant t = z`. -/
lemma extractModelℤ_atom_sat_iff (b : TBranch Atom) (ord : TimeOrdering)
    (z : ℤ) (p : Atom) :
    Satisfies (extractModelℤ b ord) z (.atom p) ↔
    b.any (fun sf => sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p) := by
  simp only [Satisfies.atom_iff, extractModelℤ]

omit [Hashable Atom] in
/-- T(atom p)@t on a branch implies atom p is satisfied in `extractModelℤ b ord`
at `ord.instant t`. -/
lemma extractModelℤ_atomPos_sat (b : TBranch Atom) (ord : TimeOrdering)
    (t : TimeIndex) (p : Atom)
    (hmem : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b) :
    Satisfies (extractModelℤ b ord) (ord.instant t) (.atom p) := by
  rw [extractModelℤ_atom_sat_iff, List.any_eq_true]
  exact ⟨⟨.pos, .atom p, t⟩, hmem, by simp⟩

omit [Hashable Atom] in
/-- ⊥ is never satisfied in any `extractModelℤ` model, at any instant. -/
lemma extractModelℤ_bot_false (b : TBranch Atom) (ord : TimeOrdering) (z : ℤ) :
    ¬ Satisfies (extractModelℤ b ord) z .bot :=
  Satisfies.bot_false (extractModelℤ b ord) z

/-! ## Bi-Lasso Periodic Countermodel (Phase 4 Spike)

`extractModelℤ` above is the "island" model: every instant not populated by an actual branch
label reads uniformly `false`. This is insufficient for the Until/Since truth lemma, which
needs a witness that may fall *beyond* the branch's last populated instant. The fix (report 01
§4, grounded by report 02 Finding 4) is a bidirectional ultimately-periodic (bi-lasso) ℤ-model:
fold every instant beyond the branch's populated range back into a finite "loop window" using
the time-subset-blocked ancestor pair the tableau's own termination argument already produces.

This section spikes the core periodic-reduction definition and a single property lemma against
it (plan discipline: confirm tractability before committing to the full redesign). The spike
takes the loop witness `(instAnc, instNew)` as an explicit hypothesis rather than deriving its
existence from `isSubsetBlocked`/the fuel-termination argument — that derivation, and the
"every instant carries a complete Hintikka time-type" helper, are separate, larger sub-tasks of
this phase. -/

/-- Periodic reduction of an integer into the loop window `[instAnc, instNew)`, using Mathlib's
`toIcoMod`. Instants at or before `instNew` are left unchanged (the populated prefix and the
first loop copy); instants beyond `instNew` are folded back by whole multiples of the loop
length `instNew - instAnc`. -/
noncomputable def periodicReduce (instAnc instNew : ℤ) (hL : instAnc < instNew) (z : ℤ) : ℤ :=
  if z ≤ instNew then z else instAnc + toIcoMod (sub_pos.mpr hL) 0 (z - instAnc)

/-- The periodic reduction always lands back inside the loop window `[instAnc, instNew)` for
instants beyond `instNew`: this is the genuinely load-bearing fact the spike needs to confirm
(not just the trivial identity-below-`instNew` case) -- `toIcoMod`'s Mathlib characterization
does the modular-arithmetic work. -/
lemma periodicReduce_mem_Ico_of_gt (instAnc instNew : ℤ) (hL : instAnc < instNew) (z : ℤ)
    (hz : instNew < z) :
    instAnc ≤ periodicReduce instAnc instNew hL z ∧
      periodicReduce instAnc instNew hL z < instNew := by
  unfold periodicReduce
  rw [if_neg (by omega)]
  have hmem := toIcoMod_mem_Ico (sub_pos.mpr hL) (0 : ℤ) (z - instAnc)
  rw [Set.mem_Ico] at hmem
  omega

/-- The bi-lasso periodic countermodel: instants at or before the loop witness `instNew` read
branch content directly (as `extractModelℤ`); instants beyond `instNew` read the periodically
reduced instant's branch content instead, so the model never "runs out" of populated content. -/
noncomputable def extractModelℤPeriodic (b : TBranch Atom) (ord : TimeOrdering)
    (instAnc instNew : ℤ) (hL : instAnc < instNew) : TemporalModel ℤ Atom where
  valuation z p := b.any fun sf =>
    sf.sign == .pos && ord.instant sf.label == periodicReduce instAnc instNew hL z &&
      sf.formula == .atom p

omit [Hashable Atom] in
/-- Spike property lemma: for instants already at or before the loop witness `instNew`, the
periodic model's atom satisfaction agrees exactly with `extractModelℤ`'s (the reduction is the
identity there). This confirms the periodic reduction is tractable and conservative over the
populated range before committing to the full Phase 4 redesign. -/
lemma extractModelℤPeriodic_atom_sat_iff_of_le (b : TBranch Atom) (ord : TimeOrdering)
    (instAnc instNew : ℤ) (hL : instAnc < instNew) (z : ℤ) (hz : z ≤ instNew) (p : Atom) :
    Satisfies (extractModelℤPeriodic b ord instAnc instNew hL) z (.atom p) ↔
    b.any (fun sf => sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p) := by
  simp only [Satisfies.atom_iff, extractModelℤPeriodic, periodicReduce, hz, if_true]

omit [Hashable Atom] in
/-- T(atom p)@t on a branch, at an instant at or before the loop witness, implies atom p is
satisfied in the periodic model at that instant. Periodic analogue of
`extractModelℤ_atomPos_sat`. -/
lemma extractModelℤPeriodic_atomPos_sat_of_le (b : TBranch Atom) (ord : TimeOrdering)
    (instAnc instNew : ℤ) (hL : instAnc < instNew) (t : TimeIndex) (p : Atom)
    (hz : ord.instant t ≤ instNew) (hmem : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b) :
    Satisfies (extractModelℤPeriodic b ord instAnc instNew hL) (ord.instant t) (.atom p) := by
  rw [extractModelℤPeriodic_atom_sat_iff_of_le b ord instAnc instNew hL (ord.instant t) hz,
    List.any_eq_true]
  exact ⟨⟨.pos, .atom p, t⟩, hmem, by simp⟩

omit [Hashable Atom] in
/-- ⊥ is never satisfied in the periodic model, at any instant. -/
lemma extractModelℤPeriodic_bot_false (b : TBranch Atom) (ord : TimeOrdering)
    (instAnc instNew : ℤ) (hL : instAnc < instNew) (z : ℤ) :
    ¬ Satisfies (extractModelℤPeriodic b ord instAnc instNew hL) z .bot :=
  Satisfies.bot_false (extractModelℤPeriodic b ord instAnc instNew hL) z

/-! ## Backward (Past-Tail) Periodic Reduction (Phase 4b)

`periodicReduce` above only extends the model *beyond* a future loop witness `instNew`. A
genuine bi-lasso countermodel needs a symmetric backward extension beyond a *past* loop
witness `pAnc`, folding instants below `pAnc` back into a past loop window `[pAnc, pNew)`.
This mirrors `periodicReduce`/`periodicReduce_mem_Ico_of_gt` exactly: the same `toIcoMod`
formula already handles negative offsets correctly, so only the guard direction flips
(identity at/after `pAnc`, fold strictly before it). -/

/-- Past-tail periodic reduction of an integer into the loop window `[pAnc, pNew)`. Instants at
or after `pAnc` are left unchanged (the loop body and everything after it); instants strictly
before `pAnc` are folded back by whole multiples of the loop length `pNew - pAnc`. Symmetric to
`periodicReduce`. -/
noncomputable def periodicReducePast (pAnc pNew : ℤ) (hL : pAnc < pNew) (z : ℤ) : ℤ :=
  if pAnc ≤ z then z else pAnc + toIcoMod (sub_pos.mpr hL) 0 (z - pAnc)

/-- The past-tail periodic reduction always lands back inside the loop window `[pAnc, pNew)`
for instants strictly before `pAnc`. Symmetric to `periodicReduce_mem_Ico_of_gt`. -/
lemma periodicReducePast_mem_Ico_of_lt (pAnc pNew : ℤ) (hL : pAnc < pNew) (z : ℤ)
    (hz : z < pAnc) :
    pAnc ≤ periodicReducePast pAnc pNew hL z ∧ periodicReducePast pAnc pNew hL z < pNew := by
  unfold periodicReducePast
  rw [if_neg (by omega)]
  have hmem := toIcoMod_mem_Ico (sub_pos.mpr hL) (0 : ℤ) (z - pAnc)
  rw [Set.mem_Ico] at hmem
  omega

/-- The past-tail periodic countermodel: instants at or after the past loop witness `pAnc`
read branch content directly (as `extractModelℤ`); instants strictly before `pAnc` read the
periodically reduced instant's branch content instead. Symmetric to `extractModelℤPeriodic`. -/
noncomputable def extractModelℤPeriodicPast (b : TBranch Atom) (ord : TimeOrdering)
    (pAnc pNew : ℤ) (hL : pAnc < pNew) : TemporalModel ℤ Atom where
  valuation z p := b.any fun sf =>
    sf.sign == .pos && ord.instant sf.label == periodicReducePast pAnc pNew hL z &&
      sf.formula == .atom p

omit [Hashable Atom] in
/-- Spike property lemma: for instants already at or after the past loop witness `pAnc`, the
past-periodic model's atom satisfaction agrees exactly with `extractModelℤ`'s (the reduction is
the identity there). Symmetric to `extractModelℤPeriodic_atom_sat_iff_of_le`. -/
lemma extractModelℤPeriodicPast_atom_sat_iff_of_ge (b : TBranch Atom) (ord : TimeOrdering)
    (pAnc pNew : ℤ) (hL : pAnc < pNew) (z : ℤ) (hz : pAnc ≤ z) (p : Atom) :
    Satisfies (extractModelℤPeriodicPast b ord pAnc pNew hL) z (.atom p) ↔
    b.any (fun sf => sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p) := by
  simp only [Satisfies.atom_iff, extractModelℤPeriodicPast, periodicReducePast, hz, if_true]

omit [Hashable Atom] in
/-- T(atom p)@t on a branch, at an instant at or after the past loop witness, implies atom p is
satisfied in the past-periodic model at that instant. Symmetric to
`extractModelℤPeriodic_atomPos_sat_of_le`. -/
lemma extractModelℤPeriodicPast_atomPos_sat_of_ge (b : TBranch Atom) (ord : TimeOrdering)
    (pAnc pNew : ℤ) (hL : pAnc < pNew) (t : TimeIndex) (p : Atom)
    (hz : pAnc ≤ ord.instant t) (hmem : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b) :
    Satisfies (extractModelℤPeriodicPast b ord pAnc pNew hL) (ord.instant t) (.atom p) := by
  rw [extractModelℤPeriodicPast_atom_sat_iff_of_ge b ord pAnc pNew hL (ord.instant t) hz,
    List.any_eq_true]
  exact ⟨⟨.pos, .atom p, t⟩, hmem, by simp⟩

omit [Hashable Atom] in
/-- ⊥ is never satisfied in the past-periodic model, at any instant. -/
lemma extractModelℤPeriodicPast_bot_false (b : TBranch Atom) (ord : TimeOrdering)
    (pAnc pNew : ℤ) (hL : pAnc < pNew) (z : ℤ) :
    ¬ Satisfies (extractModelℤPeriodicPast b ord pAnc pNew hL) z .bot :=
  Satisfies.bot_false (extractModelℤPeriodicPast b ord pAnc pNew hL) z

/-! ## Loop-Witness Conversion Helper (Phase 4a, Partial)

`periodicReduce`/`periodicReducePast` above take the loop witness `(instAnc, instNew)` (resp.
`(pAnc, pNew)`) as free parameters with a bare `hL : instAnc < instNew` hypothesis. Phase 4a's
goal is to derive this `hL` from a genuine tableau-produced constraint fact rather than assume
it abstractly. The conversion itself is immediate given `InstantStrict` and a direct ordering
edge; that part is proved below (`instantStrict_constraint_lt`). What Phase 4a does **not**
close — documented precisely in the "Blocked (FMP Existence Argument)" section following
`extractModelℤPeriodic_bot_false` above and the module docstring's "Remaining Blocked
Obligations" — is the existence of such a witnessing edge (or, more precisely, of a genuine
`isSubsetBlocked`-satisfying ancestor pair reachable among an *arbitrary* open branch's labels)
for the general case Phase 4c/4d need; see that write-up for the full analysis. -/

omit [Hashable Atom] in
/-- Direct conversion step for Phase 4a: given `InstantStrict ord` (already established
run-level, sorry-free, by `temporalTableau_instantStrict`) and a recorded ordering-constraint
edge `(t_anc, t_new) ∈ ord.constraints`, produces exactly the `hL : ord.instant t_anc <
ord.instant t_new` fact `periodicReduce`/`extractModelℤPeriodic` need, replacing the spike's
free `hL` parameter with a value derived from the tableau's own constraint bookkeeping. This is
the conversion half of Phase 4a; see the module docstring for what remains open (the existence,
for an arbitrary open branch, of such an edge tied to a genuine `isSubsetBlocked` witness). -/
lemma instantStrict_constraint_lt (ord : TimeOrdering) (t_anc t_new : TimeIndex)
    (hIS : TimeOrdering.InstantStrict ord) (hedge : (t_anc, t_new) ∈ ord.constraints) :
    ord.instant t_anc < ord.instant t_new :=
  hIS t_anc t_new hedge

/-! ## Open Branch Structure -/

omit [Hashable Atom] in
/-- An open temporal branch contains no T(⊥) signed formula. -/
lemma openBranch_noBotPos
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false) :
    ¬ ∃ t, (⟨.pos, .bot, t⟩ : TSF Atom) ∈ b := by
  intro ⟨t, hmem⟩
  -- Build the isSome witness for b.find?
  have hfind : (b.find? fun sf => sf.isPos && sf.formula == (⊥ : Formula Atom)).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨⟨.pos, .bot, t⟩, hmem, ?_⟩
    simp only [SignedFormula.isPos, Sign.isPos, Bool.true_and]
    exact beq_self_eq_true _
  -- The find? returning some makes findClassicalClosure return some
  cases hbotfind : b.find? (fun sf => sf.isPos && sf.formula == (⊥ : Formula Atom)) with
  | some sf =>
    -- findClassicalClosure b = some (.botPos sf.label)
    have hfclas : findClassicalClosure b = some (.botPos sf.label) := by
      simp [findClassicalClosure, hbotfind]
    -- isTemporalClosed = true
    have hclosed : isTemporalClosed b ord tracker = true := by
      simp [isTemporalClosed, findTemporalClosure, hfclas]
    simp [hclosed] at hopen
  | none => simp [hbotfind] at hfind

omit [Hashable Atom] in
/-- An open temporal branch has no complementary T(φ)/F(φ) pair at the same time label. -/
lemma openBranch_noContradiction
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false) :
    Branch.findContradiction b = none := by
  -- Work through the findClassicalClosure / findTemporalClosure chain
  -- Step 1: findClassicalClosure must return none (otherwise isTemporalClosed = true)
  have hfclas_none : findClassicalClosure b = none := by
    cases hfclas : findClassicalClosure b with
    | some r =>
      have hclosed : isTemporalClosed b ord tracker = true := by
        simp [isTemporalClosed, findTemporalClosure, hfclas]
      simp [hclosed] at hopen
    | none => rfl
  -- Step 2: from findClassicalClosure = none, extract Branch.findContradiction = none
  simp only [findClassicalClosure] at hfclas_none
  cases hbotfind : b.find? (fun sf => sf.isPos && sf.formula == (⊥ : Formula Atom)) with
  | some sf => simp [hbotfind] at hfclas_none
  | none =>
    simp only [hbotfind] at hfclas_none
    cases hcontra : Branch.findContradiction b with
    | some pair => simp [hcontra] at hfclas_none
    | none => rfl

omit [Hashable Atom] in
/-- F(atom p)@t on an open branch implies ¬ Satisfies (extractModel b) t (atom p).

If T(atom p)@t were also on the branch, `Branch.findContradiction` would return `some`,
contradicting `openBranch_noContradiction`. We witness the contradiction via
`List.findSome?_isSome_iff` using the positive signed formula as the search element. -/
lemma extractModel_atom_neg_notSat
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false)
    (t : TimeIndex) (p : Atom)
    (hmem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b) :
    ¬ Satisfies (extractModel b) t (.atom p) := by
  rw [extractModel_atom_sat_iff]
  intro h_any
  -- Extract a positive witness T(atom p)@t from the branch
  rw [List.any_eq_true] at h_any
  obtain ⟨sf_pos, hmem_pos, hcond⟩ := h_any
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨⟨hpos_sign, hpos_lab⟩, hpos_form⟩ := hcond
  have hsign : sf_pos.sign = .pos := LawfulBEq.eq_of_beq hpos_sign
  have hlab : sf_pos.label = t := LawfulBEq.eq_of_beq hpos_lab
  have hform : sf_pos.formula = .atom p := LawfulBEq.eq_of_beq hpos_form
  -- An open branch has no T/F contradiction pair
  have hcontra_none : Branch.findContradiction b = none :=
    openBranch_noContradiction b ord tracker hopen
  -- But sf_pos and hmem together witness a T/F pair at (atom p, t)
  -- → Branch.findContradiction b ≠ none
  have hcontra_some : (Branch.findContradiction b).isSome = true := by
    simp only [Branch.findContradiction, List.findSome?_isSome_iff]
    refine ⟨sf_pos, hmem_pos, ?_⟩
    -- Show (predicate sf_pos).isSome = true
    have hisPos : sf_pos.isPos = true := by
      simp [SignedFormula.isPos, Sign.isPos, hsign]
    -- The inner any: F(atom p)@t witnesses the negative match
    have hinner : b.any (fun sf' =>
        sf'.sign == .neg && sf'.formula == sf_pos.formula && sf'.label == sf_pos.label) = true := by
      rw [List.any_eq_true]
      exact ⟨⟨.neg, .atom p, t⟩, hmem, by simp [hform, hlab]⟩
    simp [hisPos, hinner]
  simp [hcontra_none] at hcontra_some

omit [Hashable Atom] in
/-- F(atom p)@t on an open branch implies
¬ Satisfies (extractModelℤ b ord) (ord.instant t) (atom p),
provided `ord.instant` is injective on branch labels carrying `atom p`.

This injectivity hypothesis is needed because two distinct labels `t ≠ t'` could share
an instant (`ord.instant t = ord.instant t'`); without injectivity, a T(atom p)@t' at the
same instant would make the ℤ model satisfy atom p at `ord.instant t` even when F(atom p)@t
is present. Proving injectivity of `ord.instant` on live branch labels is a separate task. -/
lemma extractModelℤ_atom_neg_notSat
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false)
    (t : TimeIndex) (p : Atom)
    (hmem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b)
    (hInj : ∀ sf ∈ b, sf.formula = .atom p → sf.sign = .pos →
            ord.instant sf.label = ord.instant t → sf.label = t) :
    ¬ Satisfies (extractModelℤ b ord) (ord.instant t) (.atom p) := by
  rw [extractModelℤ_atom_sat_iff]
  intro h_any
  rw [List.any_eq_true] at h_any
  obtain ⟨sf_pos, hmem_pos, hcond⟩ := h_any
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨⟨hpos_sign, hpos_inst⟩, hpos_form⟩ := hcond
  have hsign : sf_pos.sign = .pos := LawfulBEq.eq_of_beq hpos_sign
  have hinst : ord.instant sf_pos.label = ord.instant t := LawfulBEq.eq_of_beq hpos_inst
  have hform : sf_pos.formula = .atom p := LawfulBEq.eq_of_beq hpos_form
  have hlab : sf_pos.label = t := hInj sf_pos hmem_pos hform hsign hinst
  have hcontra_none : Branch.findContradiction b = none :=
    openBranch_noContradiction b ord tracker hopen
  have hcontra_some : (Branch.findContradiction b).isSome = true := by
    simp only [Branch.findContradiction, List.findSome?_isSome_iff]
    refine ⟨sf_pos, hmem_pos, ?_⟩
    have hisPos : sf_pos.isPos = true := by
      simp [SignedFormula.isPos, Sign.isPos, hsign]
    have hinner : b.any (fun sf' =>
        sf'.sign == .neg && sf'.formula == sf_pos.formula && sf'.label == sf_pos.label) = true := by
      rw [List.any_eq_true]
      exact ⟨⟨.neg, .atom p, t⟩, hmem, by simp [hform, hlab]⟩
    simp [hisPos, hinner]
  simp [hcontra_none] at hcontra_some

/-! ## Propositional Fragment -/

/-- The propositional fragment of `Formula Atom`: formulas built from atoms, ⊥, and →.
Does not include temporal operators (until, since). Since `and`, `or`, and `neg` are
Łukasiewicz-encoded as `imp`/`bot`, this predicate covers the full classical propositional
fragment automatically. -/
inductive IsPropositional : Formula Atom → Prop where
  /-- Atomic propositions are propositional. -/
  | atom (p : Atom) : IsPropositional (.atom p)
  /-- Falsum is propositional. -/
  | bot : IsPropositional .bot
  /-- Implication of propositional formulas is propositional. -/
  | imp {φ ψ : Formula Atom} (hφ : IsPropositional φ) (hψ : IsPropositional ψ) :
      IsPropositional (.imp φ ψ)

omit [Hashable Atom] [DecidableEq Atom] in
/-- Every formula has complexity at least 1. Used as the base-case vacuity
in strong-induction proofs: `n = 0` implies no formula has `complexity ≤ 0`. -/
private lemma Formula.one_le_complexity (φ : Formula Atom) : 1 ≤ φ.complexity := by
  unfold Formula.complexity
  split <;> omega

omit [Hashable Atom] [DecidableEq Atom] in
/-- For propositional `φ`/`ψ`, `(φ.imp ψ).complexity` always takes the "generic imp" branch
of `Formula.complexity` (never the R(φ,ψ)/T(φ,ψ) special-cased overhead-1 patterns, which
require a `.untl`/`.snce` sub-term that `IsPropositional` excludes). Used to unstick
`Formula.complexity`'s pattern match when the operands are still symbolic in strong-induction
proofs: without this, `simp [Formula.complexity]` cannot determine which match arm fires for an
abstract `φ.imp ψ`. -/
private lemma IsPropositional.complexity_imp_eq {φ ψ : Formula Atom}
    (hφ : IsPropositional φ) (hψ : IsPropositional ψ) :
    (φ.imp ψ).complexity = 1 + φ.complexity + ψ.complexity := by
  cases hφ <;> cases hψ <;> rfl

omit [Hashable Atom] in
/-- Convert a `b.any` positive membership witness to list membership. -/
private lemma any_pos_mem (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) = true) :
    (⟨.pos, φ, t⟩ : TSF Atom) ∈ b := by
  rw [List.any_eq_true] at h
  obtain ⟨sf, hmem, hcond⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  obtain ⟨⟨hsign, hlabel⟩, hform⟩ := hcond
  obtain ⟨s, fm, l⟩ := sf
  simp_all

omit [Hashable Atom] in
/-- Convert a `b.any` negative membership witness to list membership. -/
private lemma any_neg_mem (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) = true) :
    (⟨.neg, φ, t⟩ : TSF Atom) ∈ b := by
  rw [List.any_eq_true] at h
  obtain ⟨sf, hmem, hcond⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  obtain ⟨⟨hsign, hlabel⟩, hform⟩ := hcond
  obtain ⟨s, fm, l⟩ := sf
  simp_all

omit [Hashable Atom] in
/-- Convert list membership to a `b.any` positive witness. -/
private lemma mem_to_any_pos (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : (⟨.pos, φ, t⟩ : TSF Atom) ∈ b) :
    b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) = true := by
  rw [List.any_eq_true]
  exact ⟨⟨.pos, φ, t⟩, h, by simp⟩

omit [Hashable Atom] in
/-- Convert list membership to a `b.any` negative witness. -/
private lemma mem_to_any_neg (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : (⟨.neg, φ, t⟩ : TSF Atom) ∈ b) :
    b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) = true := by
  rw [List.any_eq_true]
  exact ⟨⟨.neg, φ, t⟩, h, by simp⟩

/-! ## Remaining Blocked Obligations (BLOCKED)

The following section documents proof obligations that remain blocked.
These are stated as structured goal declarations in comments.
None use `sorry` or new axioms.

### Time-Ordering Invariant: InstantStrict

**Design**: The false `ordConstraints_strict` lemma (which claimed `a < b` for all
constraint pairs `(a, b)` as Nat labels) is replaced by the correct
`InstantStrict` invariant (`TimeOrdering.lean`). See `TimeOrdering.InstantStrict`.

**The fix**: `TimeOrdering` now carries an `instant : Nat → ℤ` field. Each `addFuture t
tNew` sets `instant tNew = instant t + 1`, and each `addPast t tNew` sets
`instant tNew = instant t - 1`. The invariant `InstantStrict ord : ∀ a b, (a,b) ∈
ord.constraints → ord.instant a < ord.instant b` holds edge-by-edge from `empty`
through every `addFuture`/`addPast` (proved sorry-free in `TimeOrdering.lean`).

**Order-preservation choice**: `D = ℤ`, `f = ord.instant`. The corrected
`openBranch_branchSat` sketch (below) uses `⟨ℤ, inferInstance, inferInstance,
extractModelℤ b ord, ord.instant, hInst, …⟩` where `hInst` is the run-level
`InstantStrict ord` lemma.

**`hInst` construction**: `hInst` is a concrete, sorry-free theorem:
`Cslib.Logic.Temporal.Tableau.temporalTableau_instantStrict` (`Saturation.lean`). The
obstacle was structural: `processNext` was a `let rec` nested inside `temporalExpandBranches`,
so Lean generated no standalone recursion/induction principle for it. The fix lifts the
pair into a top-level `mutual … end` block with an explicit lexicographic `termination_by`
(`Saturation.lean`), proves a single-step preservation lemma
(`temporalStepBranch_preserves`) packaging the edge-by-edge `InstantStrict`/`OrdFreshWRT`
lemmas as the inductive step, and threads the invariant through the run via strong
induction on `fuel` plus structural induction on the worklist
(`temporalTableau_instantStrict`). The order-preservation component of `openBranch_branchSat`
is thus fully dischargeable; only the FMP-blocked truth lemma below remains.

**Why `ordConstraints_strict` is false**: `addPast t tNew` records `(tNew, t)` with
`tNew = branchNextTime b > t` (by `branchNextTime_gt`). So `(tNew, t) ∈ constraints`
but `tNew > t`, violating `∀ (a,b), a < b`. The Nat label is a fresh identifier, not
a semantic time value; `ord.instant` carries the semantic order instead.

### Propositional Truth Lemma

The Until/Since (`untl`/`snce`) cases remain FMP-blocked (see below); the propositional
fragment (atom/bot/imp) is handled here by strong induction on `Formula.complexity`. -/

omit [Hashable Atom] in
/-- Auxiliary truth lemma for the propositional fragment, bounded by a `Nat` fuel `n` so
that the proof can use strong (well-founded) induction on `Formula.complexity`: every strict
subformula of a propositional formula has strictly smaller complexity, so the single
induction hypothesis `ih` covers all (including the *deep* subformulas exposed by the
Łukasiewicz encoding of `and`/`or`/`neg`). -/
private lemma temporalTruthLemma_propositional_aux
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hH : temporalHintikkaSet b ord tracker)
    (n : Nat) :
    ∀ (φ : Formula Atom), φ.complexity ≤ n → IsPropositional φ → ∀ (t : TimeIndex),
      (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
        Satisfies (extractModel b) t φ) ∧
      (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
        ¬ Satisfies (extractModel b) t φ) := by
  obtain ⟨hopen, hrule⟩ := hH
  induction n with
  | zero =>
    intro φ hle hp t
    exact absurd hle (by have := Formula.one_le_complexity φ; omega)
  | succ n ih =>
    intro φ hle hp t
    cases hp with
    | atom p =>
      refine ⟨fun hmem => ?_, fun hmem => ?_⟩
      · exact extractModel_atomPos_sat b t p (any_pos_mem b t (.atom p) hmem)
      · exact extractModel_atom_neg_notSat b ord tracker hopen t p
          (any_neg_mem b t (.atom p) hmem)
    | bot =>
      refine ⟨fun hmem => ?_, fun _ => extractModel_bot_false b t⟩
      exact absurd ⟨t, any_pos_mem b t .bot hmem⟩
        (openBranch_noBotPos b ord tracker hopen)
    | imp hφ' hψ' =>
      -- φ = .imp φ' ψ'. The Łukasiewicz encoding means the fired rule depends on
      -- the structural shape of φ'/ψ': andPos/orPos/impPos/negPos (T) and their duals (F).
      -- Each output subformula has smaller complexity, so `ih` applies.
      refine ⟨fun hpos => ?_, fun hneg => ?_⟩
      · -- T-direction: T(imp φ' ψ') on branch → Satisfies m t (imp φ' ψ')
        simp only [Satisfies.imp_iff]
        intro hφ_sat
        have hmem := any_pos_mem b t _ hpos
        have hout := hrule _ hmem
        cases hφ' with
        | bot => exact absurd hφ_sat (Satisfies.bot_false _ _)
        | atom p =>
          cases hψ' with
          | bot =>
            -- negPos fires: linear [F(atom p)@t]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            have hfp := hout _ (List.mem_singleton_self _)
            exact absurd hφ_sat ((ih (.atom p)
              (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).2
              (mem_to_any_neg b t _ hfp))
          | atom q =>
            -- impPos fires: branching [[F(atom p)], [T(atom q)]]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · exact absurd hφ_sat ((ih (.atom p)
              (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).2
                (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
            · exact (ih (.atom q) (by simp only [Formula.complexity] at hle ⊢; omega) (.atom q) t).1
                (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
          | imp hψc hψd =>
            -- impPos fires: branching [[F(atom p)], [T(imp _ _)]]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · exact absurd hφ_sat ((ih (.atom p)
              (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).2
                (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
            · exact (ih _
              (by simp only [Formula.complexity] at hle ⊢; omega) (IsPropositional.imp hψc hψd) t).1
                (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
        | imp ha hb =>
          cases hb with
          | bot =>
            -- φ' = imp a bot (neg-shape): orPos fires: [[T(a)@t], [T(ψ')@t]]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · -- br = [T(a)@t]: sat a contradicts hφ_sat : sat a → False
              have ht_a := hbr _ (List.mem_singleton_self _)
              exact absurd ((ih _ (by simp only [Formula.complexity,
                IsPropositional.complexity_imp_eq, ha, IsPropositional.bot] at hle ⊢; omega) ha
                t).1 (mem_to_any_pos b t _ ht_a)) hφ_sat
            · -- br = [T(ψ')@t]: sat ψ'
              exact (ih _ (by simp only [Formula.complexity] at hle ⊢; omega) hψ' t).1
                (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
          | atom q =>
            -- φ' = imp a (atom q): impPos (ψ'≠bot) or negPos (ψ'=bot)
            cases hψ' with
            | bot =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              have hf := hout _ (List.mem_singleton_self _)
              exact absurd hφ_sat ((ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp ha (.atom q)) t).2
                (mem_to_any_neg b t _ hf))
            | atom r =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · exact absurd hφ_sat ((ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp ha (.atom q)) t).2
                  (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
              · exact (ih (.atom r)
                (by simp only [Formula.complexity] at hle ⊢; omega) (.atom r) t).1
                  (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
            | imp hψc hψd =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · exact absurd hφ_sat ((ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp ha (.atom q)) t).2
                  (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
              · exact (ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp hψc hψd) t).1
                  (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
          | imp hc hd =>
            cases hd with
            | bot =>
              -- φ' = imp a (imp c bot): andPos (ψ'=bot) or impPos (ψ'≠bot)
              cases hψ' with
              | bot =>
                -- andPos fires: linear [T(a)@t, T(c)@t]
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_a, ht_c, -⟩ := hout
                exact hφ_sat
                  ((ih _ (by simp only [Formula.complexity, IsPropositional.complexity_imp_eq,
                    hc, IsPropositional.bot] at hle ⊢; omega) ha t).1
                    (mem_to_any_pos b t _ ht_a))
                  ((ih _ (by simp only [Formula.complexity, IsPropositional.complexity_imp_eq,
                    hc, IsPropositional.bot] at hle ⊢; omega) hc t).1
                    (mem_to_any_pos b t _ ht_c))
              | atom r =>
                -- impPos fires
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc .bot)) t).2
                    (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih (.atom r)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom r) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc .bot)) t).2
                    (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
            | atom r =>
              -- φ' = imp a (imp c (atom r)): impPos or negPos
              cases hψ' with
              | bot =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                have hf := hout _ (List.mem_singleton_self _)
                exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).2
                  (mem_to_any_neg b t _ hf))
              | atom s =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).2
                    (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih (.atom s)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom s) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).2
                    (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
            | imp he hf =>
              -- φ' = imp a (imp c (imp e f)): impPos or negPos
              cases hψ' with
              | bot =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                have hf' := hout _ (List.mem_singleton_self _)
                exact absurd hφ_sat
                  ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (IsPropositional.imp he hf)))
                      t).2
                    (mem_to_any_neg b t _ hf'))
              | atom s =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat
                    ((ih _
                      (by simp only [Formula.complexity] at hle ⊢; omega)
                        (IsPropositional.imp ha (IsPropositional.imp hc
                          (IsPropositional.imp he hf)))
                        t).2
                      (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih (.atom s)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom s) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat
                    ((ih _
                      (by simp only [Formula.complexity] at hle ⊢; omega)
                        (IsPropositional.imp ha (IsPropositional.imp hc
                          (IsPropositional.imp he hf)))
                        t).2
                      (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
      · -- F-direction: ¬ Satisfies m t (imp φ' ψ')
        simp only [Satisfies.imp_iff]
        intro hφ_to_ψ
        have hmem := any_neg_mem b t _ hneg
        have hout := hrule _ hmem
        cases hφ' with
        | bot =>
          -- negNeg/impNeg both output T(bot)@t, contradicting openBranch
          cases hψ' with
          | bot =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              exact absurd ⟨t, hout _ List.mem_cons_self⟩ (openBranch_noBotPos b ord tracker hopen)
          | atom _ =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              exact absurd ⟨t, hout _ List.mem_cons_self⟩ (openBranch_noBotPos b ord tracker hopen)
          | imp _ _ =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              exact absurd ⟨t, hout _ List.mem_cons_self⟩ (openBranch_noBotPos b ord tracker hopen)
        | atom p =>
          cases hψ' with
          | bot =>
            -- negNeg fires: linear [T(atom p)@t]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            have ht_p := hout _ (List.mem_singleton_self _)
            exact hφ_to_ψ ((ih (.atom p)
              (by simp only [Formula.complexity] at hle ⊢; omega)
                (.atom p) t).1 (mem_to_any_pos b t _ ht_p))
          | atom q =>
            -- impNeg fires: linear [T(atom p)@t, F(atom q)@t]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            simp only [List.forall_mem_cons] at hout
            obtain ⟨ht_p, hf_q, -⟩ := hout
            exact (ih (.atom q) (by simp only [Formula.complexity] at hle ⊢; omega) (.atom q) t).2
              (mem_to_any_neg b t _ hf_q)
              (hφ_to_ψ ((ih (.atom p)
                (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).1
                (mem_to_any_pos b t _ ht_p)))
          | imp hψc hψd =>
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            simp only [List.forall_mem_cons] at hout
            obtain ⟨ht_p, hf_ψ, -⟩ := hout
            exact (ih _
              (by simp only [Formula.complexity] at hle ⊢; omega) (IsPropositional.imp hψc hψd) t).2
              (mem_to_any_neg b t _ hf_ψ)
              (hφ_to_ψ ((ih (.atom p)
                (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).1
                (mem_to_any_pos b t _ ht_p)))
        | imp ha hb =>
          cases hb with
          | bot =>
            -- φ' = imp a bot: orNeg fires: linear [F(a)@t, F(ψ')@t]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            simp only [List.forall_mem_cons] at hout
            obtain ⟨hf_a, hf_ψ, -⟩ := hout
            exact (ih _ (by simp only [Formula.complexity, IsPropositional.complexity_imp_eq,
              ha, IsPropositional.bot] at hle ⊢; omega) hψ' t).2
              (mem_to_any_neg b t _ hf_ψ)
              (hφ_to_ψ ((ih _ (by simp only [Formula.complexity,
                IsPropositional.complexity_imp_eq, ha, IsPropositional.bot] at hle ⊢; omega) ha
                t).2 (mem_to_any_neg b t _ hf_a)))
          | atom q =>
            -- φ' = imp a (atom q): negNeg (ψ'=bot) or impNeg (ψ'≠bot)
            cases hψ' with
            | bot =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              have ht := hout _ (List.mem_singleton_self _)
              exact hφ_to_ψ ((ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp ha (.atom q)) t).1
                (mem_to_any_pos b t _ ht))
            | atom r =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              simp only [List.forall_mem_cons] at hout
              obtain ⟨ht_φ, hf_ψ, -⟩ := hout
              exact (ih (.atom r) (by simp only [Formula.complexity] at hle ⊢; omega) (.atom r) t).2
                (mem_to_any_neg b t _ hf_ψ)
                (hφ_to_ψ ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (.atom q)) t).1
                  (mem_to_any_pos b t _ ht_φ)))
            | imp hψc hψd =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              simp only [List.forall_mem_cons] at hout
              obtain ⟨ht_φ, hf_ψ, -⟩ := hout
              exact (ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp hψc hψd) t).2
                (mem_to_any_neg b t _ hf_ψ)
                (hφ_to_ψ ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (.atom q)) t).1
                  (mem_to_any_pos b t _ ht_φ)))
          | imp hc hd =>
            cases hd with
            | bot =>
              -- φ' = imp a (imp c bot): andNeg (ψ'=bot) or impNeg/negNeg (ψ'≠bot)
              cases hψ' with
              | bot =>
                -- andNeg: branching [[F(a)@t], [F(c)@t]]
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · have hf_a := hbr _ (List.mem_singleton_self _)
                  exact hφ_to_ψ (fun h_a => absurd h_a ((ih _ (by simp only [Formula.complexity,
                    IsPropositional.complexity_imp_eq, hc, IsPropositional.bot] at hle ⊢; omega)
                    ha t).2 (mem_to_any_neg b t _ hf_a)))
                · have hf_c := hbr _ (List.mem_singleton_self _)
                  exact hφ_to_ψ (fun _ h_c => absurd h_c ((ih _ (by simp only [Formula.complexity,
                    IsPropositional.complexity_imp_eq, hc, IsPropositional.bot] at hle ⊢; omega)
                    hc t).2 (mem_to_any_neg b t _ hf_c)))
              | atom r =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih (.atom r)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom r) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc .bot)) t).1
                    (mem_to_any_pos b t _ ht_φ)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc .bot)) t).1
                    (mem_to_any_pos b t _ ht_φ)))
            | atom r =>
              -- φ' = imp a (imp c (atom r)): negNeg or impNeg
              cases hψ' with
              | bot =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                have ht := hout _ (List.mem_singleton_self _)
                exact hφ_to_ψ ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).1
                  (mem_to_any_pos b t _ ht))
              | atom s =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih (.atom s)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom s) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).1
                    (mem_to_any_pos b t _ ht_φ)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).1
                    (mem_to_any_pos b t _ ht_φ)))
            | imp he hf =>
              -- φ' = imp a (imp c (imp e f)): negNeg or impNeg
              cases hψ' with
              | bot =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                have ht := hout _ (List.mem_singleton_self _)
                exact hφ_to_ψ
                  ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (IsPropositional.imp he hf)))
                      t).1
                    (mem_to_any_pos b t _ ht))
              | atom s =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih (.atom s)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom s) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (IsPropositional.imp he hf)))
                      t).1
                    (mem_to_any_pos b t _ ht_φ)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (IsPropositional.imp he hf)))
                      t).1
                    (mem_to_any_pos b t _ ht_φ)))

omit [Hashable Atom] in
/-- Truth lemma for the propositional fragment (atom, ⊥, →) of the temporal tableau:
for a propositional `φ`, every `T(φ)@t` on a temporal Hintikka branch is satisfied in the
extracted model, and every `F(φ)@t` is not. Until/Since are excluded by `IsPropositional`. -/
lemma temporalTruthLemma_propositional
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hH : temporalHintikkaSet b ord tracker)
    (φ : Formula Atom) (hprop : IsPropositional φ) (t : TimeIndex) :
    (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
      Satisfies (extractModel b) t φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
      ¬ Satisfies (extractModel b) t φ) :=
  temporalTruthLemma_propositional_aux b ord tracker hH φ.complexity φ le_rfl hprop t

/-! ### Remaining FMP-Blocked Obligations

The Until/Since eventuality-fulfilment cases of the truth lemma — and hence open-branch
satisfiability, completeness, and the `Decidable (valid ·)` instance — remain blocked on
PTL's Finite Model Property, which is not yet formalized.
-/

end Cslib.Logic.Temporal.Tableau

end
