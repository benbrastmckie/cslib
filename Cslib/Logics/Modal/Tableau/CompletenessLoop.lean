/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.Completeness
public import Cslib.Logics.Modal.Tableau.Soundness
public import Cslib.Logics.Modal.Tableau.GenericDriver
public import Cslib.Logics.Modal.Tableau.S5Simplification

/-! # Modal K Tableau Completeness Loop: Combined-Invariant Single-Step Preservation

This module bundles the five loop invariants needed to run the modal K tableau's completeness
fuel-induction: world/expanded-set universe closure and the rank-map
bookkeeping (`ModalPotentialInv`, `FmpMeasure.lean`), the Φ-based world-bound witness
(`modalStepBranch_worldBound`), and the Hintikka expanded-set invariant on the branch's expanded
set (`modalStepBranch_hintikka_inv`, `Completeness.lean`). It proves that one `modalStepBranch`
step preserves this bundle on every child branch it produces, while the base-3 counting measure
(`modalExpMeasure`) strictly decreases.

## Main Definitions

- `ModalLoopInv`: the bundled per-branch loop invariant threaded across the completeness
  fuel-induction.
- `ModalLoopInvGen`: `ModalLoopInv`, generalized over an abstract
  `apply : RuleApply Atom`. Only `hintikkaInv` mentions `apply`; the other six conjuncts are
  already rule-agnostic. Bridged to `ModalLoopInv` via `ModalLoopInv_iff_gen` rather than
  identified definitionally, so `ModalLoopInv` stays byte-identical.

## Main Results

- `modalStep_preserves_invariant`: one `modalStepBranch` step preserves `ModalLoopInv` (under a
  single shared rank map `rank'`) on every child branch/expanded-set pair, and strictly decreases
  `modalExpMeasure` by at least one.
- `modalExpandBranchesGen_hintikka` (the crux): the generic top-loop Hintikka lemma,
  over an abstract `apply` and a `φ0`-indexed `RuleApplicationSpecAt φ0 apply` witness,
  concluding in `modalHintikkaSetGen apply bR aR` (not the
  concrete `modalHintikkaSet bR aR`) -- this is what lets the T, B, and S4 systems consume
  the generic Hintikka-set statement shape. `TDriver.lean`'s `modalExpandBranchesT_hintikka`
  one-liner is the structural proof this generalization succeeded. `RuleApplicationSpec` grows
  from seven fields to eleven (F8 `localShapeInvariance` through F12 `diaPosWitness`,
  `GenericDriver.lean`) to support this. K's `modalExpandBranches_hintikka`,
  `modalStep_preserves_invariant`, `ModalLoopInv`, and every other public K declaration in this
  module retain byte-identical statements, re-derived as corollaries via `modalStepBranch_eq`/
  `modalExpandBranches_eq`/`modalHintikkaSet_eq`/`ModalLoopInv_iff_gen`; `kValid`,
  `modalTableau_decides`, and `instDecidableKValid` are untouched entirely.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## The Bundled Loop Invariant -/

/-- **Bundled loop invariant** threaded across the completeness
fuel-induction: the `ModalPotentialInv` bundle (branch/expanded-set universe
closure, `acc` freshness/known-targets, out-degree correspondence, rank-map bookkeeping,
`FmpMeasure.lean:2215`), the Φ-based potential bound needed by `modalStepBranch_worldBound` to
conclude the a-priori world bound survives a step, and the Hintikka expanded-set invariant
(`modalHintikkaClause`, `Completeness.lean`) recording that every already-expanded formula's
witness obligation is already met on the branch. Bundling these lets the fuel induction carry a
single hypothesis instead of ten separate ones. -/
structure ModalLoopInv (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (rank : WorldIndex → Nat) : Prop where
  /-- The `ModalPotentialInv` bundle: universe closure, `acc` bookkeeping, rank map. -/
  potentialInv : ModalPotentialInv φ0 b e acc rank
  /-- The Φ-bound consumed by `modalStepBranch_worldBound`/`modalStepBranch_potential_step` to
  conclude the a-priori world bound is an exact loop invariant (not merely non-increasing). -/
  phiBound : modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank + 1 ≤
    geomCap (modalSubfmls φ0).length (modalDepth φ0)
  /-- Every already-expanded formula's Hintikka witness obligation is already met on `b`. -/
  hintikkaInv : ∀ sf ∈ e, modalHintikkaClause sf.sign sf.formula sf.label b acc
  /-- Every box-shaped formula in the expanded set `e` has sign `.neg` (i.e. is `boxNeg`-shaped,
  `F(□φ)@w`). Needed because `modalHintikkaClause` (used by `hintikkaInv`) is vacuously `True`
  for *any* box-shaped formula regardless of sign, whereas `modalHintikkaSet`'s second conjunct
  only carves out `.neg, .box _`; the `.pos, .box _` (`boxPos`) case genuinely needs its
  `.persistent` clause discharged. This is sound because `boxPos`'s own `modalApplyOne` result
  is always `.notApplicable` or `.persistent` (never `.linear`/`.branching`,
  `modalApplyOne_boxPos_eq` (`Rules.lean`), so a `boxPos`-shaped formula can never be the
  `sf_exp` that gets appended to `e` by a `modalStepBranch` step. -/
  eBoxOnlyNeg : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg
  /-- Every `boxNeg`-shaped formula `F(□ψ)@w` in the expanded set `e` already has a witness
  successor on the branch: `∃ w', acc.hasEdge w w' ∧ F(ψ)@w' ∈ b`. Needed for `modalHintikkaSet`'s
  third conjunct, which is a genuine existential claim not captured by `hintikkaInv`/
  `modalHintikkaClause` (vacuous for all box-shaped formulas). Sound because `boxNeg` is *always*
  applicable (`Rules.lean:115-139` never checks an emptiness guard, unlike `boxPos`/`diamondNeg`),
  so once `F(□ψ)@w` is expanded (added to `e`), its witness `F(ψ)@w'` and edge `w → w'` are
  created immediately (`modalApplyOne_boxNeg_witness` below) and persist unchanged thereafter
  (branches only grow, `acc` edges are only added). -/
  eBoxNegWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
  /-- Every diamond-shaped formula in the expanded set `e` has sign `.pos` (i.e. is
  `diamondPos`-shaped, `T(◇φ)@w`). `diamond` is a native constructor, so
  `diamondPos` genuinely mints a fresh world (symmetric to `boxNeg`) and needs the same
  sign-discrimination invariant as `eBoxOnlyNeg`: `modalHintikkaClause` is vacuously `True` for
  *any* diamond-shaped formula regardless of sign, whereas `modalHintikkaSet`'s second conjunct
  only carves out `.pos, .diamond _`; the `.neg, .diamond _` (`diamondNeg`) case genuinely needs
  its `.persistent` clause discharged. Sound because `diamondNeg`'s own `modalApplyOne` result
  is always `.notApplicable` or `.persistent` (never `.linear`/`.branching`,
  `modalApplyOne_diamondNeg_eq` (`Rules.lean`), so a `diamondNeg`-shaped formula can never be
  the `sf_exp` that gets appended to `e` by a `modalStepBranch` step. -/
  eDiamondOnlyPos : ∀ sf ∈ e, ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos
  /-- Every `diamondPos`-shaped formula `T(◇ψ)@w` in the expanded set `e` already has a witness
  successor on the branch: `∃ w', acc.hasEdge w w' ∧ T(ψ)@w' ∈ b`. Needed for `modalHintikkaSet`'s
  fourth conjunct, symmetric to `eBoxNegWitness`'s third conjunct. Sound because
  `diamondPos` is *always* applicable (`Rules.lean:93-116` never checks an emptiness guard,
  unlike `boxPos`/`diamondNeg`), so once `T(◇ψ)@w` is expanded (added to `e`), its witness
  `T(ψ)@w'` and edge `w → w'` are created immediately (`modalApplyOne_diamondPos_witness` below)
  and persist unchanged thereafter (branches only grow, `acc` edges are only added). -/
  eDiamondPosWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b

/-- **Generic bundled loop invariant**: `ModalLoopInv`, generalized over an abstract
`apply : RuleApply Atom`. Only `hintikkaInv` mentions `apply` (via `modalHintikkaClauseGen`); the
other six conjuncts are already rule-agnostic (statements mention no rule function at all). Kept
as its own `structure` (not derived from `ModalLoopInv`) to preserve K's byte-identical public
surface; bridged via `ModalLoopInv_iff_gen`. -/
structure ModalLoopInvGen (apply : RuleApply Atom) (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (rank : WorldIndex → Nat) : Prop where
  /-- The `ModalPotentialInv` bundle: universe closure, `acc` bookkeeping, rank map. -/
  potentialInv : ModalPotentialInv φ0 b e acc rank
  /-- The Φ-bound consumed by `modalStepBranch_worldBound`/`modalStepBranch_potential_step` to
  conclude the a-priori world bound is an exact loop invariant (not merely non-increasing). -/
  phiBound : modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank + 1 ≤
    geomCap (modalSubfmls φ0).length (modalDepth φ0)
  /-- Every already-expanded formula's Hintikka witness obligation is already met on `b`. -/
  hintikkaInv : ∀ sf ∈ e, modalHintikkaClauseGen apply sf.sign sf.formula sf.label b acc
  /-- Every box-shaped formula in the expanded set `e` has sign `.neg`. -/
  eBoxOnlyNeg : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg
  /-- Every `boxNeg`-shaped formula `F(□ψ)@w` in the expanded set `e` already has a witness
  successor on the branch. -/
  eBoxNegWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
  /-- Every diamond-shaped formula in the expanded set `e` has sign `.pos`. -/
  eDiamondOnlyPos : ∀ sf ∈ e, ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos
  /-- Every `diamondPos`-shaped formula `T(◇ψ)@w` in the expanded set `e` already has a witness
  successor on the branch. -/
  eDiamondPosWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b

/-- Bridge: `ModalLoopInv` and `ModalLoopInvGen modalApplyOne` are logically
equivalent (constructor/destructor on the seven fields, each field either `Iff.rfl`-trivial or
`modalHintikkaClause_eq`-rewritten). Kept as an `Iff` rather than an `abbrev`/definitional
identification so `ModalLoopInv` stays a genuinely distinct `structure` -- the anonymous
7-field destructure and `refine ⟨…⟩` constructor call sites elsewhere in this file are
unaffected. -/
theorem ModalLoopInv_iff_gen (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (rank : WorldIndex → Nat) :
    ModalLoopInv φ0 b e acc rank ↔ ModalLoopInvGen modalApplyOne φ0 b e acc rank := by
  constructor
  · intro h
    exact ⟨h.potentialInv, h.phiBound,
      fun sf hsf => modalHintikkaClause_eq sf.sign sf.formula sf.label b acc ▸
        h.hintikkaInv sf hsf,
      h.eBoxOnlyNeg, h.eBoxNegWitness, h.eDiamondOnlyPos, h.eDiamondPosWitness⟩
  · intro h
    exact ⟨h.potentialInv, h.phiBound,
      fun sf hsf => (modalHintikkaClause_eq sf.sign sf.formula sf.label b acc).symm ▸
        h.hintikkaInv sf hsf,
      h.eBoxOnlyNeg, h.eBoxNegWitness, h.eDiamondOnlyPos, h.eDiamondPosWitness⟩

/-! ## Local Helper Lemmas

These re-derive three facts that are `private` to `FmpMeasure.lean` (hence unavailable across
files): the branch-side universe closure `bClosure` survives a step (mirroring the `private`
`modalStepBranch_eClosure`'s case-split shape but driven by `modalApplyOne_outputs_subset`
instead), the expanded-set closure `eClosure` survives a step (an exact copy of
`modalStepBranch_eClosure`'s proof, since it is `private` there), and the a-priori world bound
holds directly from a Φ-bound witness (an exact copy of `modalStepBranch_worldBound`'s closing
calc chain, generalized over an arbitrary potential term `Φ` so it applies to the pre-step branch
`b` itself, not just a step's output). -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- The a-priori world bound holds for any branch `bb` whose Φ-sum (`modalMaxWorld bb + Φ`) is
bounded by `geomCap Sf (modalDepth φ0)`, for an arbitrary potential term `Φ`. Generalizes the
closing calc chain of `modalStepBranch_worldBound` (`FmpMeasure.lean:2451`) so it applies
directly to a Φ-bound hypothesis on any branch, not only to a step's output. -/
private lemma modalMaxWorld_lt_worldBound_of_phiBound
    (φ0 : Proposition Atom) (bb : List (SignedFormula (Proposition Atom) WorldIndex))
    (Φ : Nat)
    (hPhiBound : modalMaxWorld bb + Φ + 1 ≤
      geomCap (modalSubfmls φ0).length (modalDepth φ0)) :
    modalMaxWorld bb < modalWorldBound φ0 := by
  have hmwlt : modalMaxWorld bb < geomCap (modalSubfmls φ0).length (modalDepth φ0) :=
    calc modalMaxWorld bb < modalMaxWorld bb + Φ + 1 :=
          Nat.lt_succ_of_le (Nat.le_add_right (modalMaxWorld bb) Φ)
      _ ≤ geomCap (modalSubfmls φ0).length (modalDepth φ0) := hPhiBound
  have hSfpos : 1 ≤ (modalSubfmls φ0).length := modalSf_pos φ0
  have hSfdeg : (modalSubfmls φ0).length = 1 → modalDepth φ0 = 0 :=
    modalSf_one_imp_depth_zero φ0
  have hcapbound : geomCap (modalSubfmls φ0).length (modalDepth φ0) ≤
      (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) := geomCap_le_pow hSfpos hSfdeg
  have hSfle : (modalSubfmls φ0).length ≤ 2 * modalComplexity φ0 + 1 :=
    modalSubfmls_length_le φ0
  have hpow1 : (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) ≤
      (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) := Nat.pow_le_pow_left hSfle _
  have hdc : modalDepth φ0 ≤ modalComplexity φ0 := modalDepth_le_complexity φ0
  have hpow2 : (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) ≤
      (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hWB : modalWorldBound φ0 = (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) := rfl
  calc modalMaxWorld bb < geomCap (modalSubfmls φ0).length (modalDepth φ0) := hmwlt
    _ ≤ (modalSubfmls φ0).length ^ (modalDepth φ0 + 1) := hcapbound
    _ ≤ (2 * modalComplexity φ0 + 1) ^ (modalDepth φ0 + 1) := hpow1
    _ ≤ (2 * modalComplexity φ0 + 1) ^ (modalComplexity φ0 + 1) := hpow2
    _ = modalWorldBound φ0 := hWB.symm

/-! ## Rank-Free Loop Invariant via the `Aux` Parametrization

`ModalLoopInvGen` (above) threads a rank map `rank : WorldIndex → Nat` purely to re-establish
the a-priori world bound (`phiBound`) across a step, via K's exact potential-conservation
identity (`modalStepBranch_potential_step_gen`, `FmpMeasure.lean`). S5w's own termination
argument (`S5wTagInv`/`S5wWorldInv`, `S5Simplification.lean`) re-establishes the same world
bound with *no* rank map at all -- purely by tag-cardinality counting. `ModalLoopInvHintikka`
below factors the world-bound conjunct out into an abstract, caller-supplied `Aux` predicate so
both arguments can share one structure.

**The hazard this design avoids**: a bare scalar field `worldBound : modalMaxWorld b <
modalWorldBound φ0` is *not* itself step-preserved -- `n < WB` says nothing about `n + 1 < WB`.
K only re-establishes it via the exact `phiBound` conservation identity; S5w via the exact
tag-cardinality identity. `Aux` is therefore threaded as an opaque, step-preserved predicate
(`AuxStepPreserved`) from which the bound is derived pointwise (`AuxBounds`), never as a bound
scalar on its own. -/

/-- **`Aux` is preserved by one `modalStepBranchGen apply` step** (re-arity'd
to thread `e` as an explicit `Aux` argument). An adversarial audit
machine-checked that the prior `b → acc → Prop` shape is not
merely unproven at K's instantiation
but **refutable**: a minting step advances `acc` and `e` in lockstep (`acc ↦ acc.addEdge l w'`,
`e ↦ e ++ [sf]`), so an `Aux` with no `e` slot re-asserts the post-state obligation at the
*pre-state* `e`, which is false in general (not merely when the frozen and step `e` diverge --
the audit's counterexample sets them equal and it is still false). The fix restores the shape
`modalStepGen_preserves_invariant` (the port's own source of truth) always had: the conclusion
pairs each new branch with **its own** new expanded set via `newBs.zip newExps`, and `Aux` gains
an `e` slot to receive it. Given the two promoted branch-side bookkeeping facts (`accFreshInv`,
`accTargetsKnown`) every instantiation needs as ambient hypotheses: K's own step lemmas consume
`accFreshInv` (`spec.freshLocal`), and S5w's `modalStepBranchS5w_preserves_worldInv` needs
`accTargetsKnown b acc` as a documented *third* hypothesis beyond `Aux` itself (the counting-crux
deviation: K's `boxPos`/`diamondNeg` propagation shapes emit at `acc.successorsOf w`, unbounded
by `modalMaxWorld` without it). -/
def AuxStepPreserved (apply : RuleApply Atom)
    (Aux : List (SignedFormula (Proposition Atom) WorldIndex) →
           List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop) : Prop :=
  ∀ (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility),
    modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc) →
    accFreshInv b acc → accTargetsKnown b acc → Aux b e acc →
    ∀ p ∈ newBs.zip newExps, Aux p.1 p.2 newAcc

/-- **`Aux` entails the a-priori world bound**: the pointwise obligation that lets
`ModalLoopInvHintikka.aux` stand in for `ModalLoopInvGen`'s `phiBound` conjunct wherever the
world bound (`modalMaxWorld b < modalWorldBound φ0`) is needed, e.g. by
`modalExpMeasure_step_lt_gen` (`FmpMeasure.lean`) in a step-preservation port. Re-arity'd
alongside `AuxStepPreserved` to thread `e`. -/
def AuxBounds (φ0 : Proposition Atom)
    (Aux : List (SignedFormula (Proposition Atom) WorldIndex) →
           List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop) : Prop :=
  ∀ (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
    Aux b e acc → modalMaxWorld b < modalWorldBound φ0

/-- **Rank-free bundled loop invariant, `Aux`-parametrized** (a further generalization of
`ModalLoopInvGen`). Carries the five rank-free conjuncts of `ModalPotentialInv` directly
(`bClosure`, `eClosure`, `eNodup`, `accFresh`, `accKnown`) plus the five Hintikka-witness
conjuncts unchanged from `ModalLoopInvGen`, and replaces `potentialInv`/`phiBound` with a single
opaque `aux : Aux b acc` field. `rankBound`/`rankEdge`/`outDegEq` (`ModalPotentialInv`'s
remaining, genuinely rank-dependent fields) are *not* promoted here -- they live entirely inside
K's own `Aux` instantiation (`ModalLoopAuxK` below), since S5w's instantiation needs no rank map
at all. This is an arity change from `ModalLoopInvGen`'s seven `(rank : WorldIndex → Nat)`-scoped
fields, not a field rename: the flat five-field list above lives inside `ModalPotentialInv`, not
`ModalLoopInvGen`, in the pre-existing structure. -/
structure ModalLoopInvHintikka (apply : RuleApply Atom) (φ0 : Proposition Atom)
    (Aux : List (SignedFormula (Proposition Atom) WorldIndex) →
           List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) : Prop where
  /-- Every branch formula is a member of the fixed finite universe `U(φ0)`. -/
  bClosure : ∀ x ∈ b, x ∈ modalUniverse φ0
  /-- Every expanded-set formula is a member of `U(φ0)`. -/
  eClosure : ∀ x ∈ e, x ∈ modalUniverse φ0
  /-- The expanded set has no duplicate entries. -/
  eNodup : e.Nodup
  /-- All of `acc`'s recorded worlds are `< modalNextWorld b`. -/
  accFresh : accFreshInv b acc
  /-- Every `acc`-edge target is a label already appearing on the branch. -/
  accKnown : accTargetsKnown b acc
  /-- The opaque, caller-supplied auxiliary predicate standing in for the world-bound conjunct
  (`phiBound` for K, `S5wTagInv ∧ S5wWorldInv` for S5w). -/
  aux : Aux b e acc
  /-- Every already-expanded formula's Hintikka witness obligation is already met on `b`. -/
  hintikkaInv : ∀ sf ∈ e, modalHintikkaClauseGen apply sf.sign sf.formula sf.label b acc
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

/-! ### K's `Aux` Instantiation -/

/-- **K's instantiation of `Aux`**: existentially quantify over a rank map witnessing both the
remaining `ModalPotentialInv` fields (`outDegEq`, `rankBound`, `rankEdge`) and the exact
`phiBound` conservation identity. `e` is now threaded as `Aux`'s own second
argument (matching every other per-branch use of `ModalLoopInvHintikka`'s `e` parameter at the
invocation site) rather than closed over via currying -- the prior curried-`e` shape is exactly
what the adversarial audit proved makes a closed
`AuxStepPreserved` witness for this instantiation refutable, since a minting step advances `e`
but a curried-`e` `Aux` cannot observe the advance. -/
def ModalLoopAuxK (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) : Prop :=
  ∃ rank : WorldIndex → Nat, ModalPotentialInv φ0 b e acc rank ∧
    modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank + 1 ≤
      geomCap (modalSubfmls φ0).length (modalDepth φ0)

omit [DecidableEq Atom] [Hashable Atom] in
/-- **`ModalLoopAuxK` entails the world bound**: the pointwise `AuxBounds` obligation for K's
instantiation, discharged directly by the already-landed
`modalMaxWorld_lt_worldBound_of_phiBound`. -/
theorem ModalLoopAuxK_bounds (φ0 : Proposition Atom) :
    AuxBounds φ0 (ModalLoopAuxK φ0) := by
  rintro b e acc ⟨rank, -, hphi⟩
  exact modalMaxWorld_lt_worldBound_of_phiBound φ0 b _ hphi

/-- **`ModalLoopInvGen` is logically equivalent to `ModalLoopInvHintikka` at K's `Aux`**
(confirms `ModalLoopAuxK` elaborates in the strongest sense -- a full bridge, not merely a
type-check). Constructor/destructor on the shared eleven conjuncts plus `ModalPotentialInv`'s
three remaining rank-dependent fields, packaged into/out of the existential `aux` field. Note:
this bridge is stated at a single fixed `(b, e, acc)` and
so never exercises a step -- it confirms `ModalLoopAuxK` elaborates soundly, but is not itself a
step-preservation witness; that is `ModalLoopAuxK_stepPreserved` below. -/
theorem ModalLoopInvGen_iff_hintikka_auxK (apply : RuleApply Atom) (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (∃ rank, ModalLoopInvGen apply φ0 b e acc rank) ↔
      ModalLoopInvHintikka apply φ0 (ModalLoopAuxK φ0) b e acc := by
  constructor
  · rintro ⟨rank, hpot, hphi, hhint, hboxneg, hboxwit, hdiapos, hdiawit⟩
    exact ⟨hpot.bClosure, hpot.eClosure, hpot.eNodup, hpot.accFresh, hpot.accKnown,
      ⟨rank, hpot, hphi⟩, hhint, hboxneg, hboxwit, hdiapos, hdiawit⟩
  · rintro ⟨-, -, -, -, -, ⟨rank, hpot, hphi⟩, hhint, hboxneg, hboxwit, hdiapos, hdiawit⟩
    exact ⟨rank, hpot, hphi, hhint, hboxneg, hboxwit, hdiapos, hdiawit⟩

/-! ### S5w's `Aux` Instantiation -/

/-- **S5w's instantiation of `Aux`**: the landed tag/world invariants (`S5Simplification.lean`),
needing no rank map at all. The trailing `Accessibility` argument, and the `e` argument, are
required by `Aux`'s shared signature
(`AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka` all expect
`List (SignedFormula …) → List (SignedFormula …) → Accessibility → Prop`) but genuinely unused
here. -/
@[nolint unusedArguments]
def ModalLoopAuxS5w (φ₀ : Proposition Atom)
    (b _e : List (SignedFormula (Proposition Atom) WorldIndex)) (_acc : Accessibility) : Prop :=
  S5wTagInv φ₀ b ∧ S5wWorldInv φ₀ b

omit [Hashable Atom] in
/-- **`ModalLoopAuxS5w` entails the world bound**: the pointwise `AuxBounds` obligation for S5w's
instantiation, discharged directly by the already-landed `modalMaxWorld_lt_worldBound_of_S5w`. -/
theorem ModalLoopAuxS5w_bounds (φ₀ : Proposition Atom) :
    AuxBounds φ₀ (ModalLoopAuxS5w φ₀) := by
  rintro b e acc ⟨-, hW⟩
  exact modalMaxWorld_lt_worldBound_of_S5w hW

/-- **`ModalLoopAuxS5w` is step-preserved**: the `AuxStepPreserved` obligation for S5w's
instantiation, discharged directly by the already-landed
`modalStepBranchS5w_preserves_worldInv`, which is exactly this statement's conclusion under the
same three hypotheses (`hT`/`hW` packaged as `Aux`, `hK` the `accTargetsKnown` ambient). The
conclusion now ranges over `newBs.zip newExps` rather than bare `newBs`;
`(List.of_mem_zip hp).1` replaces the prior direct `hb'` membership, the only change this
instantiation needs. Unlike K's instantiation, this discharges completely here: no rank map, no
potential, no further step-preservation machinery needed. -/
theorem ModalLoopAuxS5w_stepPreserved (φ₀ : Proposition Atom) :
    AuxStepPreserved modalApplyOneS5w (ModalLoopAuxS5w φ₀) := by
  rintro b e acc newBs newExps newAcc hstep _hFresh hKnown ⟨hT, hW⟩ p hp
  exact modalStepBranchS5w_preserves_worldInv hT hW hKnown hstep p.1 (List.of_mem_zip hp).1

/-- **S5w's initial-configuration rank-free loop invariant**: `ModalLoopInvHintikka` holds of the
starting worklist entry `([F(φ₀)@0], [], ∅)`. The S5w analogue of `modalLoopInvGen_initial`, and
the last input `modalExpandBranchesHintikka` needs to deliver S5 completeness.

Cheaper than K's initial lemma, because S5w's `Aux` carries no rank map and no potential: the
five expanded-set conjuncts are all vacuous over `e = []`, `accFresh`/`accKnown` hold of the
empty relation, and the `aux` field reduces to two one-line facts -- `S5wTagInv` because the sole
branch formula is `(.neg, φ₀)` and `φ₀ ∈ modalSubfmls φ₀`, and `S5wWorldInv` because
`modalMaxWorld [F(φ₀)@0] = 0`, which bounds any cardinality. -/
lemma modalLoopInvHintikkaS5w_initial (φ₀ : Proposition Atom) :
    ModalLoopInvHintikka modalApplyOneS5w φ₀ (ModalLoopAuxS5w φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      Accessibility.empty := by
  have hmemU : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalUniverse φ₀ := by
    simp only [modalUniverse, List.mem_flatMap, List.mem_range]
    exact ⟨0, Nat.succ_pos _, φ₀, modalSubfmls_self_mem φ₀, by simp⟩
  refine ⟨?_, by simp, List.nodup_nil, accFreshInv_empty _, ?_, ⟨?_, ?_⟩,
    by simp, by simp, by simp, by simp, by simp⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hmemU
  · intro w w' hedge
    simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
    exact absurd hedge (by decide)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp only [signedSubfmls, Finset.mem_product, List.mem_toFinset]
    exact ⟨by simp, modalSubfmls_self_mem φ₀⟩
  · simp only [S5wWorldInv, modalMaxWorld, List.foldl_cons, List.foldl_nil]
    exact Nat.zero_le _

/-- **Generic branch-side universe-closure preservation**:
`modalLoopGen_bClosure`, over an abstract `(apply, spec)`, discharged by
`spec.outputsSubsetUniverse`. Body is `modalLoop_bClosure`'s exact proof with
`modalApplyOne ↦ apply`, `modalStepBranch ↦ modalStepBranchGen apply`, and
`modalApplyOne_outputs_subset ↦ spec.outputsSubsetUniverse`. -/
private lemma modalLoopGen_bClosure
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hAccInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverse φ0 := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hclosure := spec.outputsSubsetUniverse φ0 sf b acc hb hsfmem hAccInv hW
  rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x hx
    · exact hb x hx
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x (List.mem_flatten.mpr ⟨br, hbrmem, hx⟩)
    · exact hb x hx
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x hx
    · exact hb x hx
  · rw [hfstc] at hsf; simp at hsf

/-- Preservation of the branch-side universe closure across a `modalStepBranch` step: every
formula on each child branch stays inside `U(φ0)`, combining the source branch-closure `hb` with
`modalApplyOne_outputs_subset` (P1) applied to the consumed formula. Mirrors the shallow
top-level case split of the `private` `modalStepBranch_eClosure` (`FmpMeasure.lean:2166`), but
for the branch side rather than the expanded-set side.

Byte-identical-statement corollary of `modalLoopGen_bClosure` via `modalStepBranch_eq`
and K's `modalApplyOne_spec`. -/
private lemma modalLoop_bClosure
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hAccInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverse φ0 :=
  modalLoopGen_bClosure modalApplyOne modalApplyOne_spec φ0 b e acc newBs newExps newAcc
    (modalStepBranch_eq b e acc ▸ hstep) hb hAccInv hW

/-- **Generic constant-expanded-set fact**: `modalStepBranchGen_newExps_const`, over
an abstract `apply`. Takes **no** field -- driver-structural. -/
lemma modalStepBranchGen_newExps_const
    (apply : RuleApply Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc)) :
    ∃ newExp, newExps = newBs.map (fun _ => newExp) := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -⟩ := hsf
    exact ⟨e ++ [sf], rfl⟩
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -⟩ := hsf
    exact ⟨e ++ [sf], by simp [List.map_map, Function.comp_def]⟩
  · rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -⟩ := hsf
    exact ⟨e, rfl⟩
  · rw [hfstc] at hsf; simp at hsf

/-- Every `modalStepBranch` step produces children that all share the same freshly-expanded
set `newExp` (either `e` unchanged, for the `.persistent` case, or `e ++ [sf]`, for the
`.linear`/`.branching` cases), i.e. `newExps` is exactly `newBs.map (fun _ => newExp)`. This is
the generic fact `modalExpMeasure_step_lt`'s hypothesis shape (`FmpMeasure.lean:3029`) assumes as
given; here it is derived from a generic `hstep`.

Byte-identical-statement corollary of `modalStepBranchGen_newExps_const` via
`modalStepBranch_eq`. -/
private lemma modalStepBranch_newExps_const
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc)) :
    ∃ newExp, newExps = newBs.map (fun _ => newExp) :=
  modalStepBranchGen_newExps_const modalApplyOne b e acc newBs newExps newAcc
    (modalStepBranch_eq b e acc ▸ hstep)

/-- **Generic F9 discharge**: `modalLoopGen_eBoxOnlyNeg`, over an abstract
`(apply, spec)`. The statement mentions no `apply` at all (already rule-agnostic); only the
proof needs `spec.boxPosNotExpanding` (F9) to rule out `sf_exp`'s result being
`.linear`/`.branching` when it is `boxPos`-shaped -- the payload (`out`/`kForms`) is discarded
either way, which is exactly why F9's existential-payload form (rather than K's concrete
`boxPropagation`) suffices unchanged here. -/
private lemma modalLoopGen_eBoxOnlyNeg
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg) :
    ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ ψ, sf.formula = .box ψ → sf.sign = .neg := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newExps = [e ++ [sf_exp]]
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hspos : sf.sign = .pos := by cases hs : sf.sign with
        | pos => rfl
        | neg => exact absurd hs hcon
      have hform_exp : sf_exp.formula = Proposition.box ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.pos := by rw [← heq]; exact hspos
      rcases spec.boxPosNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- branching: newExps = brs.map (fun _ => e ++ [sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hspos : sf.sign = .pos := by cases hs : sf.sign with
        | pos => rfl
        | neg => exact absurd hs hcon
      have hform_exp : sf_exp.formula = Proposition.box ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.pos := by rw [← heq]; exact hspos
      rcases spec.boxPosNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- persistent: newExps = [e] (unchanged)
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact he
  · rw [hfstc] at hsf; simp at hsf

/-- Preservation of the `eBoxOnlyNeg` invariant across a `modalStepBranch` step: mirrors
`modalStepBranch_eClosure`'s case split, but for the persistent case the new expanded set is exactly
the old one (`eBoxOnlyNeg` transfers directly), while for the linear/branching cases the freshly
appended `sf_exp` must itself have sign `.neg` whenever its formula is box-shaped — since if
`sf_exp` were `.pos`-box-shaped, `modalApplyOne_boxPos_eq` would force its own result to be
`.notApplicable`/`.persistent`, contradicting the linear/branching case split.

Byte-identical-statement corollary of `modalLoopGen_eBoxOnlyNeg` via
`modalStepBranch_eq`. -/
private lemma modalLoop_eBoxOnlyNeg
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg) :
    ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ ψ, sf.formula = .box ψ → sf.sign = .neg :=
  modalLoopGen_eBoxOnlyNeg modalApplyOne modalApplyOne_spec b e acc newBs newExps newAcc
    (modalStepBranch_eq b e acc ▸ hstep) he

/-- **Generic F10 discharge**: `modalLoopGen_eDiamondOnlyPos`, dual of
`modalLoopGen_eBoxOnlyNeg` via `spec.diaNegNotExpanding`. -/
private lemma modalLoopGen_eDiamondOnlyPos
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos) :
    ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newExps = [e ++ [sf_exp]]
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hsneg : sf.sign = .neg := by cases hs : sf.sign with
        | neg => rfl
        | pos => exact absurd hs hcon
      have hform_exp : sf_exp.formula = Proposition.diamond ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.neg := by rw [← heq]; exact hsneg
      rcases spec.diaNegNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- branching: newExps = brs.map (fun _ => e ++ [sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hsneg : sf.sign = .neg := by cases hs : sf.sign with
        | neg => rfl
        | pos => exact absurd hs hcon
      have hform_exp : sf_exp.formula = Proposition.diamond ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.neg := by rw [← heq]; exact hsneg
      rcases spec.diaNegNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- persistent: newExps = [e] (unchanged)
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact he
  · rw [hfstc] at hsf; simp at hsf

/-- Preservation of the `eDiamondOnlyPos` invariant across a `modalStepBranch` step: mirrors
`modalLoop_eBoxOnlyNeg`'s case split (`diamondNeg` is the symmetric never-linear/
branching shape, dismissed via `modalApplyOne_diamondNeg_eq`).

Byte-identical-statement corollary of `modalLoopGen_eDiamondOnlyPos` via
`modalStepBranch_eq`. -/
private lemma modalLoop_eDiamondOnlyPos
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos) :
    ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos :=
  modalLoopGen_eDiamondOnlyPos modalApplyOne modalApplyOne_spec b e acc newBs newExps newAcc
    (modalStepBranch_eq b e acc ▸ hstep) he

/-- An existing accessibility edge survives adding a new one. -/
private lemma hasEdge_addEdge_mono {acc : Accessibility} {w w' x y : WorldIndex}
    (h : acc.hasEdge w w' = true) : (acc.addEdge x y).hasEdge w w' = true := by
  simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
  simp [h]

/-- **Generic accessibility-edge monotonicity**: `modalApplyGen_hasEdge_mono`, over an
abstract `apply`, given the raw `hFreshLocal` hypothesis (`RuleApplicationSpec`'s existing F1
`freshLocal` field, `GenericDriver.lean`). **No new field** -- `freshLocal`'s own dichotomy is
exactly what the deleted `modalLoop_snd_eq_or_addEdge` restated verbatim for K, so this
generalizes directly from it plus the rule-agnostic `hasEdge_addEdge_mono` above. -/
private lemma modalApplyGen_hasEdge_mono
    (apply : RuleApply Atom)
    (hFreshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (apply sf b acc).snd.hasEdge w w' = true := by
  rcases hFreshLocal sf b acc with heq | ⟨wsf, rest, -, heq⟩
  · rw [heq]; exact h
  · rw [heq]; exact hasEdge_addEdge_mono h

/-- Accessibility edges only grow across one `modalApplyOne` application: an edge present
before the step is still present in the (possibly-updated) accessibility relation afterward.

Byte-identical-statement corollary of `modalApplyGen_hasEdge_mono` via K's own
`modalApplyOne_fresh_local`. -/
private lemma modalApplyOne_hasEdge_mono
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (modalApplyOne sf b acc).snd.hasEdge w w' = true :=
  modalApplyGen_hasEdge_mono modalApplyOne modalApplyOne_fresh_local sf b acc h

/-- **Generic F11+freshLocal discharge**: `modalLoopGen_eBoxNegWitness`, over an
abstract `(apply, spec)`. For old `e`-elements the witness/edge from `he` transfers to every
child branch/accessibility via `b ⊆ b'` (branches only grow) and `modalApplyGen_hasEdge_mono`
(`spec.freshLocal`, `acc`-edges only grow); for a freshly-appended `sf_exp` that is itself
`boxNeg`-shaped, `spec.boxNegWitness'` (F11') constructs the witness and edge directly. -/
private lemma modalLoopGen_eBoxNegWitness
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', newAcc.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b' := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newBs = [nf ++ b], newExps = [e ++ [sf_exp]], newAcc from apply's snd
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply spec.freshLocal sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨w', hsndeq, rest, hfsteq⟩ := spec.boxNegWitness' b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      simp only [RuleResult.linear.injEq] at hfstc
      refine ⟨w', ?_, ?_⟩
      · rw [hnewAcc, hsfexp_eq, hsndeq]
        simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, beq_self_eq_true,
          Bool.true_and, Bool.true_or]
      · rw [← hfstc]
        exact List.mem_append.mpr (Or.inl (List.mem_cons_self))
  · -- branching: newBs = brs.map (·++b), newExps = brs.map (fun _=>e++[sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp hb'
    rw [← hsf.2.1] at he'; obtain ⟨x', -, rfl⟩ := List.mem_map.mp he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply spec.freshLocal sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨w', hsndeq, rest, hfsteq⟩ := spec.boxNegWitness' b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      -- boxNeg's own result is `.linear`, never `.branching`: contradiction
      simp at hfstc
  · -- persistent: newBs = [nf ++ b], newExps = [e] (unchanged), newAcc = acc
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
    exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply spec.freshLocal sf_exp b acc hedge,
      List.mem_append.mpr (Or.inr hwit)⟩
  · rw [hfstc] at hsf; simp at hsf

/-- Preservation of the `eBoxNegWitness` invariant across a `modalStepBranch` step: mirrors
`modalLoop_eBoxOnlyNeg`'s case split. For old `e`-elements the witness/edge from `he` transfers
to every child branch/accessibility via `b ⊆ b'` (branches only grow) and
`modalApplyOne_hasEdge_mono` (`acc`-edges only grow); for a freshly-appended `sf_exp` that is
itself `boxNeg`-shaped, `modalApplyOne_boxNeg_witness` constructs the witness and edge directly.

Byte-identical-statement corollary of `modalLoopGen_eBoxNegWitness` via
`modalStepBranch_eq`. -/
private lemma modalLoop_eBoxNegWitness
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', newAcc.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b' :=
  modalLoopGen_eBoxNegWitness modalApplyOne modalApplyOne_spec b e acc newBs newExps newAcc
    (modalStepBranch_eq b e acc ▸ hstep) he

/-- **Generic F12+freshLocal discharge**: `modalLoopGen_eDiamondPosWitness`, dual of
`modalLoopGen_eBoxNegWitness` via `spec.diaPosWitness'` (F12'). -/
private lemma modalLoopGen_eDiamondPosWitness
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', newAcc.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b' := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newBs = [nf ++ b], newExps = [e ++ [sf_exp]], newAcc from apply's snd
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply spec.freshLocal sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨w', hsndeq, rest, hfsteq⟩ := spec.diaPosWitness' b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      simp only [RuleResult.linear.injEq] at hfstc
      refine ⟨w', ?_, ?_⟩
      · rw [hnewAcc, hsfexp_eq, hsndeq]
        simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, beq_self_eq_true,
          Bool.true_and, Bool.true_or]
      · rw [← hfstc]
        exact List.mem_append.mpr (Or.inl (List.mem_cons_self))
  · -- branching: newBs = brs.map (·++b), newExps = brs.map (fun _=>e++[sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp hb'
    rw [← hsf.2.1] at he'; obtain ⟨x', -, rfl⟩ := List.mem_map.mp he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply spec.freshLocal sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨w', hsndeq, rest, hfsteq⟩ := spec.diaPosWitness' b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      -- diamondPos's own result is `.linear`, never `.branching`: contradiction
      simp at hfstc
  · -- persistent: newBs = [nf ++ b], newExps = [e] (unchanged), newAcc = acc
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
    exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply spec.freshLocal sf_exp b acc hedge,
      List.mem_append.mpr (Or.inr hwit)⟩
  · rw [hfstc] at hsf; simp at hsf

/-- Preservation of the `eDiamondPosWitness` invariant across a `modalStepBranch` step: mirrors
`modalLoop_eBoxNegWitness`'s case split (`diamondPos` is the symmetric fresh-world
witness rule, via `modalApplyOne_diamondPos_witness`).

Byte-identical-statement corollary of `modalLoopGen_eDiamondPosWitness` via
`modalStepBranch_eq`. -/
private lemma modalLoop_eDiamondPosWitness
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', newAcc.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b' :=
  modalLoopGen_eDiamondPosWitness modalApplyOne modalApplyOne_spec b e acc newBs newExps newAcc
    (modalStepBranch_eq b e acc ▸ hstep) he

/-! ## Step Preservation for `ModalLoopInvHintikka`

The five rule-dependent helpers above (`modalLoopGen_bClosure`, `_eBoxOnlyNeg`,
`_eDiamondOnlyPos`, `_eBoxNegWitness`, `_eDiamondPosWitness`) are declared against the full
`RuleApplicationSpec`, but each proof body only ever consumes a Core field
(`outputsSubsetUniverse`, `boxPosNotExpanding`, `diaNegNotExpanding`, `freshLocal`,
`boxNegWitness'`/`diaPosWitness'`). This section lands five purely-additive `_core`-suffixed
twins -- identical proof bodies, parametrized over `RuleApplicationSpecCoreAt φ0` directly --
leaving every existing declaration above untouched. The generalization pass that instead
*weakens* declarations in place (narrowing their own hypothesis from `RuleApplicationSpecCore`/
`RuleApplicationSpec` to the `φ0`-indexed `RuleApplicationSpecCoreAt φ0`/`RuleApplicationSpecAt
φ0` interface) has since happened for the declarations below this section
(`modalStepHintikka_preserves_inv` through `modalExpandBranchesGen_hintikka`), unblocking the D
driver's reuse of the top-loop Hintikka chain. -/

private lemma modalLoopGen_bClosure_core
    (apply : RuleApply Atom) (φ0 : Proposition Atom)
    (hcore : RuleApplicationSpecCoreAt φ0 apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hAccInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverse φ0 := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hclosure := hcore.outputsSubsetUniverse sf b acc hb hsfmem hAccInv hW
  rcases hfstc : (apply sf b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x hx
    · exact hb x hx
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x (List.mem_flatten.mpr ⟨br, hbrmem, hx⟩)
    · exact hb x hx
  · rw [hfstc] at hsf hclosure
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb'
    rw [← hsf.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hclosure x hx
    · exact hb x hx
  · rw [hfstc] at hsf; simp at hsf

private lemma modalLoopGen_eBoxOnlyNeg_core
    (apply : RuleApply Atom) {φ0 : Proposition Atom}
    (hcore : RuleApplicationSpecCoreAt φ0 apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg) :
    ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ ψ, sf.formula = .box ψ → sf.sign = .neg := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newExps = [e ++ [sf_exp]]
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hspos : sf.sign = .pos := by cases hsg : sf.sign with
        | pos => rfl
        | neg => exact absurd hsg hcon
      have hform_exp : sf_exp.formula = Proposition.box ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.pos := by rw [← heq]; exact hspos
      rcases hcore.boxPosNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- branching: newExps = brs.map (fun _ => e ++ [sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hspos : sf.sign = .pos := by cases hsg : sf.sign with
        | pos => rfl
        | neg => exact absurd hsg hcon
      have hform_exp : sf_exp.formula = Proposition.box ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.pos := by rw [← heq]; exact hspos
      rcases hcore.boxPosNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- persistent: newExps = [e] (unchanged)
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact he
  · rw [hfstc] at hsf; simp at hsf

private lemma modalLoopGen_eDiamondOnlyPos_core
    (apply : RuleApply Atom) {φ0 : Proposition Atom}
    (hcore : RuleApplicationSpecCoreAt φ0 apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos) :
    ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newExps = [e ++ [sf_exp]]
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hsneg : sf.sign = .neg := by cases hsg : sf.sign with
        | neg => rfl
        | pos => exact absurd hsg hcon
      have hform_exp : sf_exp.formula = Proposition.diamond ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.neg := by rw [← heq]; exact hsneg
      rcases hcore.diaNegNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- branching: newExps = brs.map (fun _ => e ++ [sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp he'
    intro sf hsfin ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | heq
    · exact he sf hsfin ψ hψ
    · by_contra hcon
      have hsneg : sf.sign = .neg := by cases hsg : sf.sign with
        | neg => rfl
        | pos => exact absurd hsg hcon
      have hform_exp : sf_exp.formula = Proposition.diamond ψ := by rw [← heq]; exact hψ
      have hsign_exp : sf_exp.sign = Sign.neg := by rw [← heq]; exact hsneg
      rcases hcore.diaNegNotExpanding sf_exp hsign_exp ψ hform_exp b acc with h | ⟨_, h⟩ <;>
        rw [h] at hfstc <;> simp at hfstc
  · -- persistent: newExps = [e] (unchanged)
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro e' he'
    rw [← hsf.2.1] at he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact he
  · rw [hfstc] at hsf; simp at hsf

private lemma modalLoopGen_eBoxNegWitness_core
    (apply : RuleApply Atom) {φ0 : Proposition Atom}
    (hcore : RuleApplicationSpecCoreAt φ0 apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', newAcc.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b' := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newBs = [nf ++ b], newExps = [e ++ [sf_exp]], newAcc from apply's snd
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply hcore.freshLocal sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨w', hsndeq, rest, hfsteq⟩ := hcore.boxNegWitness' b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      simp only [RuleResult.linear.injEq] at hfstc
      refine ⟨w', ?_, ?_⟩
      · rw [hnewAcc, hsfexp_eq, hsndeq]
        simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, beq_self_eq_true,
          Bool.true_and, Bool.true_or]
      · rw [← hfstc]
        exact List.mem_append.mpr (Or.inl (List.mem_cons_self))
  · -- branching: newBs = brs.map (·++b), newExps = brs.map (fun _=>e++[sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp hb'
    rw [← hsf.2.1] at he'; obtain ⟨x', -, rfl⟩ := List.mem_map.mp he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply hcore.freshLocal sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨w', hsndeq, rest, hfsteq⟩ := hcore.boxNegWitness' b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      -- boxNeg's own result is `.linear`, never `.branching`: contradiction
      simp at hfstc
  · -- persistent: newBs = [nf ++ b], newExps = [e] (unchanged), newAcc = acc
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
    exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply hcore.freshLocal sf_exp b acc hedge,
      List.mem_append.mpr (Or.inr hwit)⟩
  · rw [hfstc] at hsf; simp at hsf

private lemma modalLoopGen_eDiamondPosWitness_core
    (apply : RuleApply Atom) {φ0 : Proposition Atom}
    (hcore : RuleApplicationSpecCoreAt φ0 apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (he : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, ∀ sf ∈ e', ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', newAcc.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b' := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · -- linear: newBs = [nf ++ b], newExps = [e ++ [sf_exp]], newAcc from apply's snd
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply hcore.freshLocal sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨w', hsndeq, rest, hfsteq⟩ := hcore.diaPosWitness' b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      simp only [RuleResult.linear.injEq] at hfstc
      refine ⟨w', ?_, ?_⟩
      · rw [hnewAcc, hsfexp_eq, hsndeq]
        simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, beq_self_eq_true,
          Bool.true_and, Bool.true_or]
      · rw [← hfstc]
        exact List.mem_append.mpr (Or.inl (List.mem_cons_self))
  · -- branching: newBs = brs.map (·++b), newExps = brs.map (fun _=>e++[sf_exp])
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp hb'
    rw [← hsf.2.1] at he'; obtain ⟨x', -, rfl⟩ := List.mem_map.mp he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    simp only [List.mem_append, List.mem_singleton] at hsfin
    rcases hsfin with hsfin | hsfeq2
    · obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
      exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply hcore.freshLocal sf_exp b acc hedge,
        List.mem_append.mpr (Or.inr hwit)⟩
    · have hsfexp_eq : sf_exp =
          (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
        rw [← hsfeq2]; exact hsfeq
      obtain ⟨w', hsndeq, rest, hfsteq⟩ := hcore.diaPosWitness' b acc ψ w
      rw [hsfexp_eq, hfsteq] at hfstc
      -- diamondPos's own result is `.linear`, never `.branching`: contradiction
      simp at hfstc
  · -- persistent: newBs = [nf ++ b], newExps = [e] (unchanged), newAcc = acc
    rw [hfstc] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    intro b' hb' e' he' sf hsfin ψ w hsfeq
    rw [← hsf.1] at hb'; simp only [List.mem_singleton] at hb'; subst hb'
    rw [← hsf.2.1] at he'; simp only [List.mem_singleton] at he'; subst he'
    have hnewAcc : newAcc = (apply sf_exp b acc).snd := hsf.2.2.symm
    obtain ⟨w', hedge, hwit⟩ := he sf hsfin ψ w hsfeq
    exact ⟨w', hnewAcc ▸ modalApplyGen_hasEdge_mono apply hcore.freshLocal sf_exp b acc hedge,
      List.mem_append.mpr (Or.inr hwit)⟩
  · rw [hfstc] at hsf; simp at hsf

/-- **Step preservation for `ModalLoopInvHintikka`**: a port of
`modalStepGen_preserves_invariant` to the rank-free, `Aux`-parametrized invariant, with the two
`potential_step`-derived lines (the existential rank witness and the `phiBound` re-derivation)
removed and replaced by the caller-supplied `AuxStepPreserved`/`AuxBounds` facts. Only needs
`RuleApplicationSpecCoreAt φ0` -- no `rankStep`/`outDegStep`/`knownWorldsStep`. The measure-drop
consumes `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean`) directly against `hs`'s three raw Core
fields, bypassing the full-spec-typed `modalStepBranchGen_expMeasure_step_lt` wrapper. -/
lemma modalStepHintikka_preserves_inv
    (apply : RuleApply Atom) (φ0 : Proposition Atom)
    (hs : RuleApplicationSpecCoreAt φ0 apply)
    (Aux : List (SignedFormula (Proposition Atom) WorldIndex) →
           List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop)
    (hAuxStep : AuxStepPreserved apply Aux) (hAuxBounds : AuxBounds φ0 Aux)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalLoopInvHintikka apply φ0 Aux b e acc) :
    (∀ p ∈ newBs.zip newExps, ModalLoopInvHintikka apply φ0 Aux p.1 p.2 newAcc) ∧
      modalExpMeasure (modalUniverse φ0) newBs newExps + 1 ≤
        modalExpMeasure (modalUniverse φ0) [b] [e] := by
  obtain ⟨hbC, heC, heN, hFresh, hKnown, haux, hhint, hboxneg, hboxwit, hdiapos, hdiawit⟩ := hinv
  have hWb : modalMaxWorld b < modalWorldBound φ0 := hAuxBounds b e acc haux
  have hAuxAll : ∀ p ∈ newBs.zip newExps, Aux p.1 p.2 newAcc :=
    hAuxStep b e acc newBs newExps newAcc hstep hFresh hKnown haux
  have hFreshAll : ∀ b' ∈ newBs, accFreshInv b' newAcc :=
    modalStepBranch_preserves_accFreshInv_gen apply hs.freshLocal b e acc newBs newExps newAcc
      hstep hFresh
  have hKnownAll : ∀ b' ∈ newBs, accTargetsKnown b' newAcc :=
    modalStepBranch_preserves_accTargetsKnown_gen apply hs.freshLocal b e acc newBs newExps newAcc
      hstep hKnown
  have hNodupAll : ∀ e' ∈ newExps, e'.Nodup :=
    modalStepBranch_preserves_expandedNodup_gen apply b e acc newBs newExps newAcc hstep heN
  have hBClosureAll : ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverse φ0 :=
    modalLoopGen_bClosure_core apply φ0 hs b e acc newBs newExps newAcc hstep hbC hFresh hWb
  have hEClosureAll : ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverse φ0 :=
    modalStepBranch_eClosure_gen apply φ0 b e acc newBs newExps newAcc hstep hbC heC
  have hHintikkaAll :=
    modalStepBranchGen_hintikka_inv apply hs.localShapeInvariance b e acc newBs newExps newAcc
      hstep hhint
  have hBoxNegAll := modalLoopGen_eBoxOnlyNeg_core apply hs b e acc newBs newExps newAcc hstep
    hboxneg
  have hBoxWitAll := modalLoopGen_eBoxNegWitness_core apply hs b e acc newBs newExps newAcc hstep
    hboxwit
  have hDiaPosAll := modalLoopGen_eDiamondOnlyPos_core apply hs b e acc newBs newExps newAcc hstep
    hdiapos
  have hDiaWitAll := modalLoopGen_eDiamondPosWitness_core apply hs b e acc newBs newExps newAcc
    hstep hdiawit
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    exact ⟨hBClosureAll p.1 hp1, hEClosureAll p.2 hp2, hNodupAll p.2 hp2,
      hFreshAll p.1 hp1, hKnownAll p.1 hp1, hAuxAll p hp,
      hHintikkaAll p hp, hBoxNegAll p.2 hp2, hBoxWitAll p.1 hp1 p.2 hp2,
      hDiaPosAll p.2 hp2, hDiaWitAll p.1 hp1 p.2 hp2⟩
  · obtain ⟨newExp, hNewExpEq⟩ :=
      modalStepBranchGen_newExps_const apply b e acc newBs newExps newAcc hstep
    have hstep' : modalStepBranchGen apply b e acc =
        some (newBs, newBs.map (fun _ => newExp), newAcc) := by
      rw [hNewExpEq] at hstep; exact hstep
    have hdrop := modalExpMeasure_step_lt_gen apply hs.branchingLength hs.persistentFresh φ0
      hs.outputsSubsetUniverse [] [] newBs [] [] newExp b e acc newAcc rfl hbC hFresh hWb
      hstep'
    simp only [List.nil_append, List.append_nil] at hdrop
    rw [hNewExpEq]
    exact hdrop

/-- **`modalStepHintikka_preserves_inv` instantiated at S5w's `Aux`**: concretely discharges the
generic lemma above at `Aux := ModalLoopAuxS5w φ0`, using the already-landed
`modalApplyOneS5w_specCore`, `ModalLoopAuxS5w_stepPreserved`, and `ModalLoopAuxS5w_bounds` (both
above, in this file). `ModalLoopAuxS5w` ignores its `e` argument entirely, since S5w's
tag/world invariants need no rank map. -/
theorem modalStepHintikka_preserves_inv_S5w
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneS5w b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalLoopInvHintikka modalApplyOneS5w φ0 (ModalLoopAuxS5w φ0) b e acc) :
    (∀ p ∈ newBs.zip newExps,
      ModalLoopInvHintikka modalApplyOneS5w φ0 (ModalLoopAuxS5w φ0) p.1 p.2 newAcc) ∧
      modalExpMeasure (modalUniverse φ0) newBs newExps + 1 ≤
        modalExpMeasure (modalUniverse φ0) [b] [e] :=
  modalStepHintikka_preserves_inv modalApplyOneS5w φ0 (modalApplyOneS5w_specCore.toAt φ0)
    (ModalLoopAuxS5w φ0) (ModalLoopAuxS5w_stepPreserved φ0) (ModalLoopAuxS5w_bounds φ0) b e acc
    newBs newExps newAcc hstep hinv

/-- **`modalStepHintikka_preserves_inv` instantiated at K's `Aux`**: unlike
S5w, this instantiation is **generic over any `apply` with a `RuleApplicationSpecAt φ0`
witness** -- not per-logic -- so K, T, and B all get their `AuxStepPreserved` witness from this
one theorem. This is the intended "K/T/B pay nothing" guarantee, actually delivered here. Every
field is discharged by a landed, public lemma: `spec.toCore`-parametrized `_core` twins (above,
themselves typed at `RuleApplicationSpecCoreAt φ0`) for the five rule-dependent conjuncts,
`modalStepBranch_potential_step_gen` (`FmpMeasure.lean`) for the rank witness and
`rankBound`/`rankEdge`/`phiBound` conservation, and -- the crux --
`modalStepBranch_preserves_outDegEq_gen`, whose conclusion is already stated at the **new**
expanded set `p.2` (`∀ e' ∈ newExps, ∀ w, outDeg newAcc w = (e'.filter …).length`), exactly what
the re-arity'd `Aux` can now consume where the old curried-`e` shape could not. -/
theorem ModalLoopAuxK_stepPreserved (apply : RuleApply Atom) (φ0 : Proposition Atom)
    (spec : RuleApplicationSpecAt φ0 apply) :
    AuxStepPreserved apply (ModalLoopAuxK φ0) := by
  rintro b e acc newBs newExps newAcc hstep hFresh hKnown ⟨rank, hpot, hphi⟩ p hp
  obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
  obtain ⟨rank', _hagree, hrb', hre', hpotid⟩ :=
    modalStepBranch_potential_step_gen apply spec.freshLocal spec.rankStep spec.outDegStep
      spec.knownWorldsStep φ0 b e acc newBs newExps newAcc rank hstep hpot
  have hWb : modalMaxWorld b < modalWorldBound φ0 :=
    ModalLoopAuxK_bounds φ0 b e acc ⟨rank, hpot, hphi⟩
  refine ⟨rank', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact modalLoopGen_bClosure_core apply φ0 spec.toCore b e acc newBs newExps newAcc hstep
      hpot.bClosure hFresh hWb p.1 hp1
  · exact modalStepBranch_preserves_expandedNodup_gen apply b e acc newBs newExps newAcc hstep
      hpot.eNodup p.2 hp2
  · exact modalStepBranch_eClosure_gen apply φ0 b e acc newBs newExps newAcc hstep hpot.bClosure
      hpot.eClosure p.2 hp2
  · exact modalStepBranch_preserves_accFreshInv_gen apply spec.freshLocal b e acc newBs newExps
      newAcc hstep hFresh p.1 hp1
  · exact modalStepBranch_preserves_accTargetsKnown_gen apply spec.freshLocal b e acc newBs
      newExps newAcc hstep hKnown p.1 hp1
  -- THE CRUX: `outDegEq` now lands at `p.2` (the branch's OWN new `e`), not at a frozen `e`.
  · exact modalStepBranch_preserves_outDegEq_gen apply spec.outDegStep b e acc newBs newExps
      newAcc hstep hpot.outDegEq p.2 hp2
  · exact hrb' p.1 hp1
  · exact hre'
  · rw [hpotid p.1 hp1]; exact hphi

/-! ## The Parametric Top-Loop Hintikka Lemma -/

/-- **Parametric top-loop Hintikka lemma**: the `Aux`-parametrized analogue of
`modalExpandBranchesGen_hintikka` (below), built on `modalStepHintikka_preserves_inv`
the same way that lemma is itself built on `modalStepGen_preserves_invariant`. Takes only
`RuleApplicationSpecCoreAt φ0` (no `rankStep`/`outDegStep`/`knownWorldsStep`) plus the
caller-supplied `Aux`/`AuxStepPreserved`/`AuxBounds` triple in place of a rank witness; the
per-index hypothesis is `ModalLoopInvHintikka apply φ0 Aux bi ei ai` (no existential `rank`), not
`∃ rank, ModalLoopInvGen apply φ0 bi ei ai rank`.

A pure substitution port of `modalExpandBranchesGen_hintikka`'s proof: `spec ↦ hs`, the rank
witness `↦` `Aux`'s opaque `aux` field, `modalStepGen_preserves_invariant ↦
modalStepHintikka_preserves_inv`, `modalMaxWorld_lt_worldBound_of_phiBound ↦ hAuxBounds` (direct
application to `hinv.aux`), and `modalStepBranchGen_expMeasure_step_lt ↦
modalExpMeasure_step_lt_gen` (direct against `hs`'s three raw Core fields, exactly as
`modalStepHintikka_preserves_inv`'s own measure-drop already does). The only other change is that
`spec.boxNegWitness'`/`spec.diaPosWitness'` become `hs.boxNegWitness'`/`hs.diaPosWitness'` --
both are `RuleApplicationSpecCore` fields (F11'/F12'), so this needs no extra hypothesis.

`modalExpandBranchesGen_hintikka` itself is re-derived from this lemma at
`Aux := ModalLoopAuxK φ0` (see its proof below), which is what pins this factoring as faithful to
the K-facing statement its `TDriver`/`BDriver` consumers depend on. -/
theorem modalExpandBranchesHintikka
    (apply : RuleApply Atom) (φ0 : Proposition Atom)
    (hs : RuleApplicationSpecCoreAt φ0 apply)
    (Aux : List (SignedFormula (Proposition Atom) WorldIndex) →
           List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop)
    (hAuxStep : AuxStepPreserved apply Aux) (hAuxBounds : AuxBounds φ0 Aux)
    (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      modalExpMeasure (modalUniverse φ0) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        ModalLoopInvHintikka apply φ0 Aux bi ei ai) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSetGen apply bR aR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs hlen hlenA hfuel _hInv bR aR h
    have hm : modalExpMeasure (modalUniverse φ0) branches expandedSets = 0 :=
      Nat.le_zero.mp hfuel
    have hbranches : branches = [] := by
      rcases branches with _ | ⟨bh, bt⟩
      · rfl
      · exfalso
        rcases expandedSets with _ | ⟨e, es⟩
        · simp only [List.length_nil, List.length_cons] at hlen; omega
        · simp only [modalExpMeasure, List.zip_cons_cons, List.map_cons, List.sum_cons] at hm
          have h3 := Nat.one_le_pow (modalWork (modalUniverse φ0) bh e) 3 (by omega)
          omega
    subst hbranches
    simp [modalExpandBranchesGen] at h
  | succ fuel' ih =>
    intro branches expandedSets accs hlen hlenA hfuel hInv bR aR h
    simp only [modalExpandBranchesGen] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
            (ai : Accessibility),
          (done ++ pending)[i]? = some bi → (doneExp ++ pendingExp)[i]? = some ei →
          (doneAccs ++ pendingAccs)[i]? = some ai →
          ModalLoopInvHintikka apply φ0 Aux bi ei ai) →
        modalExpMeasure (modalUniverse φ0) (done ++ pending) (doneExp ++ pendingExp) ≤
          fuel' + 1 →
        modalExpandBranchesGen.processNext apply fuel' pending pendingExp pendingAccs done doneExp
            doneAccs = .openBranch bR aR →
        modalHintikkaSetGen apply bR aR from
      key branches expandedSets accs [] [] [] hlen hlenA rfl rfl hInv hfuel
        (by simpa [modalExpandBranchesGen] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs done doneExp doneAccs _ _ _ _ _ _ hinner
      simp [modalExpandBranchesGen.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hlength_p hlenP_accs hdlength hdAccs hInv_all hmeas hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength_p hlenP_accs
          simp only [modalExpandBranchesGen.processNext] at hinner
          by_cases hcl : isModalClosed bh = true
          · -- Closed branch: skip and recurse on the inner induction
            rw [if_pos hcl] at hinner
            apply ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
            · simpa using hlength_p
            · simpa using hlenP_accs
            · simp [hdlength]
            · simp [hdAccs]
            · intro i bi ei ai hib hie hia
              apply hInv_all i bi ei ai
              · convert hib using 2; simp
              · convert hie using 2; simp
              · convert hia using 2; simp
            · convert hmeas using 2 <;> simp
            · exact hinner
          · simp only [Bool.not_eq_true] at hcl
            rw [if_neg (by simp [hcl])] at hinner
            cases hstep : modalStepBranchGen apply bh e a with
            | none =>
              -- Saturated open branch: bh/a are the returned bR/aR
              rw [hstep] at hinner
              obtain ⟨hbeq, haeq⟩ : bh = bR ∧ a = aR := by
                cases hinner; exact ⟨rfl, rfl⟩
              have hbeq' : bR = bh := hbeq.symm
              have haeq' : aR = a := haeq.symm
              subst hbeq'; subst haeq'
              have hbh_idx : (done ++ bR :: bt)[done.length]? = some bR := by
                rw [List.getElem?_append_right (Nat.le_refl done.length)]; simp [Nat.sub_self]
              have he_idx : (doneExp ++ e :: es)[done.length]? = some e := by
                rw [List.getElem?_append_right (by omega)]; simp [hdlength, Nat.sub_self]
              have ha_idx : (doneAccs ++ aR :: restAs)[done.length]? = some aR := by
                rw [List.getElem?_append_right (by omega)]; simp [hdAccs, Nat.sub_self]
              have hinv := hInv_all done.length bR e aR hbh_idx he_idx ha_idx
              refine ⟨hcl, ?_, ?_, ?_⟩
              · -- Conjunct 2: rule-application clause for every sf ∈ bR
                intro sf hsfmem
                obtain ⟨s, φ, l⟩ := sf
                cases φ with
                | atom p =>
                  rcases modalStepBranchGen_none_saturated apply hstep ⟨s, .atom p, l⟩ hsfmem
                    with hine | hna
                  · have hc := hinv.hintikkaInv ⟨s, .atom p, l⟩ hine
                    simp only [modalHintikkaClauseGen] at hc
                    cases s <;> exact hc
                  · cases s <;> simp [hna]
                | bot =>
                  rcases modalStepBranchGen_none_saturated apply hstep ⟨s, .bot, l⟩ hsfmem
                    with hine | hna
                  · have hc := hinv.hintikkaInv ⟨s, .bot, l⟩ hine
                    simp only [modalHintikkaClauseGen] at hc
                    cases s <;> exact hc
                  · cases s <;> simp [hna]
                | imp a c =>
                  rcases modalStepBranchGen_none_saturated apply hstep ⟨s, .imp a c, l⟩ hsfmem
                    with hine | hna
                  · have hc := hinv.hintikkaInv ⟨s, .imp a c, l⟩ hine
                    simp only [modalHintikkaClauseGen] at hc
                    cases s <;> exact hc
                  · cases s <;> simp [hna]
                | and a c =>
                  rcases modalStepBranchGen_none_saturated apply hstep ⟨s, .and a c, l⟩ hsfmem
                    with hine | hna
                  · have hc := hinv.hintikkaInv ⟨s, .and a c, l⟩ hine
                    simp only [modalHintikkaClauseGen] at hc
                    cases s <;> exact hc
                  · cases s <;> simp [hna]
                | or a c =>
                  rcases modalStepBranchGen_none_saturated apply hstep ⟨s, .or a c, l⟩ hsfmem
                    with hine | hna
                  · have hc := hinv.hintikkaInv ⟨s, .or a c, l⟩ hine
                    simp only [modalHintikkaClauseGen] at hc
                    cases s <;> exact hc
                  · cases s <;> simp [hna]
                | box ψ' =>
                  cases s with
                  | pos =>
                    -- boxPos still falls into `_, _`; `eBoxOnlyNeg` rules out `sf ∈ e`
                    rcases modalStepBranchGen_none_saturated apply hstep ⟨.pos, .box ψ', l⟩ hsfmem
                      with hine | hna
                    · exact absurd (hinv.eBoxOnlyNeg ⟨.pos, .box ψ', l⟩ hine ψ' rfl) (by simp)
                    · simp [hna]
                  | neg =>
                    -- boxNeg = F(□ψ')@w: matches `modalHintikkaSetGen`'s first branch directly
                    trivial
                | diamond ψ' =>
                  cases s with
                  | pos =>
                    -- diamondPos = T(◇ψ')@w: matches `modalHintikkaSetGen`'s second branch
                    -- directly (native diamond, symmetric to boxNeg above).
                    trivial
                  | neg =>
                    -- diamondNeg still falls into `_, _`; `eDiamondOnlyPos` rules out `sf ∈ e`
                    rcases modalStepBranchGen_none_saturated apply hstep ⟨.neg, .diamond ψ', l⟩
                        hsfmem with hine | hna
                    · exact absurd (hinv.eDiamondOnlyPos ⟨.neg, .diamond ψ', l⟩ hine ψ' rfl)
                        (by simp)
                    · simp [hna]
              · -- Conjunct 3: box-negative witness existence
                intro ψ' w hmem
                rcases modalStepBranchGen_none_saturated apply hstep _ hmem with hine | hna
                · exact hinv.eBoxNegWitness _ hine ψ' w rfl
                · exfalso
                  obtain ⟨_, -, rest, hlin⟩ := hs.boxNegWitness' bR aR ψ' w
                  rw [hlin] at hna
                  simp at hna
              · -- Conjunct 4: diamond-positive witness existence (symmetric to
                -- Conjunct 3 above).
                intro ψ' w hmem
                rcases modalStepBranchGen_none_saturated apply hstep _ hmem with hine | hna
                · exact hinv.eDiamondPosWitness _ hine ψ' w rfl
                · exfalso
                  obtain ⟨_, -, rest, hlin⟩ := hs.diaPosWitness' bR aR ψ' w
                  rw [hlin] at hna
                  simp at hna
            | some step =>
              obtain ⟨newBs, newExps, newAcc⟩ := step
              rw [hstep] at hinner
              have hstepEq : modalStepBranchGen apply bh e a = some (newBs, newExps, newAcc) :=
                hstep
              have hinv :=
                hInv_all done.length bh e a
                  (by rw [List.getElem?_append_right (Nat.le_refl done.length)]
                      simp [Nat.sub_self])
                  (by rw [List.getElem?_append_right (by omega)]; simp [hdlength, Nat.sub_self])
                  (by rw [List.getElem?_append_right (by omega)]; simp [hdAccs, Nat.sub_self])
              obtain ⟨newExp, hNewExpEq⟩ :=
                modalStepBranchGen_newExps_const apply bh e a newBs newExps newAcc hstepEq
              subst hNewExpEq
              have hstepEq' :
                  modalStepBranchGen apply bh e a =
                    some (newBs, newBs.map (fun _ => newExp), newAcc) :=
                hstepEq
              obtain ⟨hinvAll, -⟩ :=
                modalStepHintikka_preserves_inv apply φ0 hs Aux hAuxStep hAuxBounds bh e a newBs
                  (newBs.map (fun _ => newExp)) newAcc hstepEq' hinv
              have hWb : modalMaxWorld bh < modalWorldBound φ0 := hAuxBounds bh e a hinv.aux
              have hstep_lt := modalExpMeasure_step_lt_gen apply hs.branchingLength
                hs.persistentFresh φ0 hs.outputsSubsetUniverse done bt newBs doneExp es newExp
                bh e a newAcc hdlength.symm hinv.bClosure hinv.accFresh hWb hstepEq'
              apply ih (done ++ newBs ++ bt) (doneExp ++ newBs.map (fun _ => newExp) ++ es)
                (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
              · simp only [List.length_append, List.length_map, hdlength]
                omega
              · simp only [List.length_append, List.length_replicate, hdAccs]
                omega
              · omega
              · intro i bi ei ai hib hie hia
                rcases Nat.lt_or_ge i done.length with hlt1 | hge1
                · apply hInv_all i bi ei ai
                  · rw [List.append_assoc, List.getElem?_append_left hlt1] at hib
                    rwa [List.getElem?_append_left hlt1]
                  · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hie
                    rwa [List.getElem?_append_left (by omega)]
                  · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hia
                    rwa [List.getElem?_append_left (by omega)]
                · rcases Nat.lt_or_ge i (done.length + newBs.length) with hlt2 | hge2
                  · -- Region: newBs (all sharing newExp/newAcc)
                    have hj : i - done.length < newBs.length := by omega
                    have hbi_newBs : newBs[i - done.length]? = some bi := by
                      rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                      rwa [List.getElem?_append_left hj] at hib
                    have hbi_mem : bi ∈ newBs := List.mem_of_getElem? hbi_newBs
                    have hei_eq : ei = newExp := by
                      rw [List.append_assoc,
                          List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                      rw [List.getElem?_append_left
                            (by simp only [List.length_map]; omega)] at hie
                      rw [List.getElem?_map,
                          show newBs[i - doneExp.length]? = some bi from by
                            rw [show i - doneExp.length = i - done.length from by omega]
                            exact hbi_newBs] at hie
                      simp only [Option.map_some, Option.some.injEq] at hie
                      exact hie.symm
                    have hei_eq' : newExp = ei := hei_eq.symm
                    subst hei_eq'
                    have hai_eq : ai = newAcc := by
                      rw [List.append_assoc,
                          List.getElem?_append_right (by omega : doneAccs.length ≤ i)] at hia
                      rw [List.getElem?_append_left
                            (by simp only [List.length_replicate]; omega)] at hia
                      exact List.eq_of_mem_replicate (List.mem_of_getElem? hia)
                    subst hai_eq
                    have hexp_idx : (newBs.map (fun _ => newExp))[i - done.length]? =
                        some newExp := by
                      rw [List.getElem?_map, hbi_newBs]; rfl
                    have hzip_idx :
                        (newBs.zip (newBs.map (fun _ => newExp)))[i - done.length]? =
                          some (bi, newExp) :=
                      List.getElem?_zip_eq_some.mpr ⟨hbi_newBs, hexp_idx⟩
                    exact hinvAll (bi, newExp) (List.mem_of_getElem? hzip_idx)
                  · -- Region: bt (shifted index)
                    have hbi_bt : bt[i - done.length - newBs.length]? = some bi := by
                      rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                      rw [List.getElem?_append_right
                            (by omega : newBs.length ≤ i - done.length)] at hib
                      exact hib
                    have hei_es : es[i - done.length - newBs.length]? = some ei := by
                      rw [List.append_assoc,
                          List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                      rw [List.getElem?_append_right
                            (by simp only [List.length_map]; omega :
                              (newBs.map (fun _ => newExp)).length ≤ i - doneExp.length)] at hie
                      rwa [show i - doneExp.length - (newBs.map (fun _ => newExp)).length =
                            i - done.length - newBs.length from by
                          simp only [List.length_map]; omega] at hie
                    have hai_restAs : restAs[i - done.length - newBs.length]? = some ai := by
                      rw [List.append_assoc, List.getElem?_append_right (by omega :
                            doneAccs.length ≤ i)] at hia
                      rw [List.getElem?_append_right
                            (by simp only [List.length_replicate]; omega :
                              (List.replicate newBs.length newAcc).length ≤
                                i - doneAccs.length)] at hia
                      rwa [show i - doneAccs.length -
                            (List.replicate newBs.length newAcc).length =
                            i - done.length - newBs.length from by
                          simp only [List.length_replicate]; omega] at hia
                    apply hInv_all (done.length + 1 + (i - done.length - newBs.length)) bi ei ai
                    · rw [List.getElem?_append_right
                            (by omega : done.length ≤
                              done.length + 1 + (i - done.length - newBs.length))]
                      rw [show done.length + 1 + (i - done.length - newBs.length) - done.length
                            = (i - done.length - newBs.length) + 1 from by omega]
                      rw [List.getElem?_cons_succ]; exact hbi_bt
                    · rw [List.getElem?_append_right
                            (by omega : doneExp.length ≤
                              done.length + 1 + (i - done.length - newBs.length))]
                      rw [show done.length + 1 + (i - done.length - newBs.length) -
                            doneExp.length = (i - done.length - newBs.length) + 1 from by omega]
                      rw [List.getElem?_cons_succ]; exact hei_es
                    · rw [List.getElem?_append_right
                            (by omega : doneAccs.length ≤
                              done.length + 1 + (i - done.length - newBs.length))]
                      rw [show done.length + 1 + (i - done.length - newBs.length) -
                            doneAccs.length = (i - done.length - newBs.length) + 1 from by omega]
                      rw [List.getElem?_cons_succ]; exact hai_restAs
              · exact hinner

/-! ## The Combined-Invariant Single-Step Preservation Lemma -/

/-- **Generic combined-invariant single-step preservation** (the composition crux):
`modalStepGen_preserves_invariant`, over an abstract `(apply, spec)`. Composes exactly eight
step lemmas -- seven already available as bundled `(apply, spec)` forms
(`modalStepBranchGen_potential_step`, `_preserves_accTargetsKnown`, `_preserves_outDegEq`,
`modalStepBranch_preserves_expandedNodup_gen` [no field], `_eClosure`, `_expMeasure_step_lt`, and
the rule-agnostic `modalMaxWorld_lt_worldBound_of_phiBound`); the eighth,
`modalStepBranch_preserves_accFreshInv_gen`, comes from `Soundness.lean`, called with
`spec.freshLocal`. The five rule-dependent conjuncts (`modalLoopGen_bClosure`,
`modalStepBranchGen_hintikka_inv` [raw F8, `spec.localShapeInvariance`],
`modalLoopGen_eBoxOnlyNeg`/`_eBoxNegWitness`/`_eDiamondOnlyPos`/`_eDiamondPosWitness`) are
declared above. -/
lemma modalStepGen_preserves_invariant
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (rank : WorldIndex → Nat)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalLoopInvGen apply φ0 b e acc rank) :
    ∃ rank' : WorldIndex → Nat,
      (∀ p ∈ newBs.zip newExps, ModalLoopInvGen apply φ0 p.1 p.2 newAcc rank') ∧
      modalExpMeasure (modalUniverse φ0) newBs newExps + 1 ≤
        modalExpMeasure (modalUniverse φ0) [b] [e] := by
  obtain ⟨hpot, hphi, hhint, hboxneg, hboxwit, hdiapos, hdiawit⟩ := hinv
  have hWb : modalMaxWorld b < modalWorldBound φ0 :=
    modalMaxWorld_lt_worldBound_of_phiBound φ0 b _ hphi
  obtain ⟨rank', -, hrb', hre', hpotential⟩ :=
    modalStepBranchGen_potential_step apply spec φ0 b e acc newBs newExps newAcc rank hstep hpot
  have hFreshAll : ∀ b' ∈ newBs, accFreshInv b' newAcc :=
    modalStepBranch_preserves_accFreshInv_gen apply spec.freshLocal b e acc newBs newExps newAcc
      hstep hpot.accFresh
  have hKnownAll : ∀ b' ∈ newBs, accTargetsKnown b' newAcc :=
    modalStepBranchGen_preserves_accTargetsKnown apply spec b e acc newBs newExps newAcc hstep
      hpot.accKnown
  have hOutDegAll : ∀ e' ∈ newExps, ∀ w, outDeg newAcc w =
      (e'.filter (fun x => x.label == w && isMintingShaped x)).length :=
    modalStepBranchGen_preserves_outDegEq apply spec b e acc newBs newExps newAcc hstep
      hpot.outDegEq
  have hNodupAll : ∀ e' ∈ newExps, e'.Nodup :=
    modalStepBranch_preserves_expandedNodup_gen apply b e acc newBs newExps newAcc hstep
      hpot.eNodup
  have hBClosureAll : ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverse φ0 :=
    modalLoopGen_bClosure apply spec φ0 b e acc newBs newExps newAcc hstep hpot.bClosure
      hpot.accFresh hWb
  have hEClosureAll : ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverse φ0 :=
    modalStepBranchGen_eClosure apply spec φ0 b e acc newBs newExps newAcc hstep hpot.bClosure
      hpot.eClosure
  have hHintikkaAll :=
    modalStepBranchGen_hintikka_inv apply spec.localShapeInvariance b e acc newBs newExps newAcc
      hstep hhint
  have hBoxNegAll := modalLoopGen_eBoxOnlyNeg apply spec b e acc newBs newExps newAcc hstep hboxneg
  have hBoxWitAll :=
    modalLoopGen_eBoxNegWitness apply spec b e acc newBs newExps newAcc hstep hboxwit
  have hDiaPosAll :=
    modalLoopGen_eDiamondOnlyPos apply spec b e acc newBs newExps newAcc hstep hdiapos
  have hDiaWitAll :=
    modalLoopGen_eDiamondPosWitness apply spec b e acc newBs newExps newAcc hstep hdiawit
  refine ⟨rank', ?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    exact ⟨⟨hBClosureAll p.1 hp1, hNodupAll p.2 hp2, hEClosureAll p.2 hp2,
        hFreshAll p.1 hp1, hKnownAll p.1 hp1, hOutDegAll p.2 hp2, hrb' p.1 hp1, hre'⟩,
      by rw [hpotential p.1 hp1]; exact hphi, hHintikkaAll p hp, hBoxNegAll p.2 hp2,
      hBoxWitAll p.1 hp1 p.2 hp2, hDiaPosAll p.2 hp2, hDiaWitAll p.1 hp1 p.2 hp2⟩
  · obtain ⟨newExp, hNewExpEq⟩ :=
      modalStepBranchGen_newExps_const apply b e acc newBs newExps newAcc hstep
    have hstep' : modalStepBranchGen apply b e acc =
        some (newBs, newBs.map (fun _ => newExp), newAcc) := by
      rw [hNewExpEq] at hstep; exact hstep
    have hdrop := modalStepBranchGen_expMeasure_step_lt apply spec φ0 [] [] newBs [] [] newExp b e
      acc newAcc rfl hpot.bClosure hpot.accFresh hWb hstep'
    simp only [List.nil_append, List.append_nil] at hdrop
    rw [hNewExpEq]
    exact hdrop

/-- **Combined-invariant single-step preservation**: given the bundled loop
invariant `ModalLoopInv` holds pre-step and `modalStepBranch b e acc = some (newBs, newExps,
newAcc)`, there is a single shared rank map `rank'` under which the bundle holds on every child
branch/expanded-set pair, and the base-3 counting measure `modalExpMeasure` strictly decreases.
Composes P2 (`modalStepBranch_worldBound`, `modalStepBranch_potential_step`), P3
(`modalExpMeasure_step_lt`, supplying its `hb`/`hInv`/`hW` hypotheses from the bundle), P4
(`modalStepBranch_hintikka_inv`), and the green `modalStepBranch_preserves_accFreshInv`.

Byte-identical-statement corollary of `modalStepGen_preserves_invariant` via
`modalStepBranch_eq`/`ModalLoopInv_iff_gen`. -/
lemma modalStep_preserves_invariant
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (rank : WorldIndex → Nat)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalLoopInv φ0 b e acc rank) :
    ∃ rank' : WorldIndex → Nat,
      (∀ p ∈ newBs.zip newExps, ModalLoopInv φ0 p.1 p.2 newAcc rank') ∧
      modalExpMeasure (modalUniverse φ0) newBs newExps + 1 ≤
        modalExpMeasure (modalUniverse φ0) [b] [e] := by
  obtain ⟨rank', hAll, hmeas⟩ :=
    modalStepGen_preserves_invariant modalApplyOne modalApplyOne_spec φ0 b e acc rank newBs
      newExps newAcc (modalStepBranch_eq b e acc ▸ hstep)
      ((ModalLoopInv_iff_gen φ0 b e acc rank).mp hinv)
  exact ⟨rank', fun p hp => (ModalLoopInv_iff_gen φ0 p.1 p.2 newAcc rank').mpr (hAll p hp), hmeas⟩

/-! ## The Top-Loop Hintikka Lemma -/

/-- **Generic top-loop Hintikka lemma** (the crux): if `modalExpandBranchesGen apply`
returns an open branch, that branch (with its accessibility relation) is a **generic** modal
Hintikka set, `modalHintikkaSetGen apply bR aR` -- **not** the concrete `modalHintikkaSet bR aR`.
This is the acceptance-critical conclusion type: `modalHintikkaSetGen` is spec-free
(`Saturation.lean`), so the B and S4 systems can consume this statement shape at their own
`apply`, and T's one-liner discharge (`TDriver.lean`) is the structural proof this criterion was
met.

**Now a corollary of `modalExpandBranchesHintikka`** (above), instantiated at K's own
`Aux := ModalLoopAuxK φ0`. This statement is unchanged from -- and its consumers
(`TDriver.lean`, `BDriver.lean`) are unaffected by -- the earlier ~290-line double induction it
replaces: that induction turned out to be the `Aux := ModalLoopAuxK φ0` special case of the
parametric lift, so re-deriving it here both eliminates the duplicate and serves as the standing
regression check that the parametric factoring is faithful to the K-facing contract. Three pieces
bridge the gap: `spec.toCore` (`RuleApplicationSpecAt.toCore`, `GenericDriver.lean`) projects the
`φ0`-indexed `RuleApplicationSpecAt φ0 apply` this lemma's own hypothesis carries down to the
`RuleApplicationSpecCoreAt φ0` the parametric lift asks for,
`ModalLoopAuxK_stepPreserved`/`ModalLoopAuxK_bounds` supply the `Aux` obligations,
and `ModalLoopInvGen_iff_hintikka_auxK` converts this statement's per-index
`∃ rank, ModalLoopInvGen …` hypothesis into the lift's rank-free `ModalLoopInvHintikka …`.

The semantically-loaded reasoning (the saturated-leaf discharge against F9-F12 of
`RuleApplicationSpec`, `GenericDriver.lean`) now lives once, in the parametric lift. -/
lemma modalExpandBranchesGen_hintikka
    (apply : RuleApply Atom) (φ0 : Proposition Atom)
    (spec : RuleApplicationSpecAt φ0 apply) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      modalExpMeasure (modalUniverse φ0) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        ∃ rank, ModalLoopInvGen apply φ0 bi ei ai rank) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSetGen apply bR aR := by
  intro branches expandedSets accs hlen hlenA hfuel hInv bR aR h
  exact modalExpandBranchesHintikka apply φ0 spec.toCore (ModalLoopAuxK φ0)
    (ModalLoopAuxK_stepPreserved apply φ0 spec) (ModalLoopAuxK_bounds φ0) fuel
    branches expandedSets accs hlen hlenA hfuel
    (fun i bi ei ai hb he ha =>
      (ModalLoopInvGen_iff_hintikka_auxK apply φ0 bi ei ai).mp (hInv i bi ei ai hb he ha))
    bR aR h

/-- **Top-loop Hintikka lemma**: if `modalExpandBranches` returns an open
branch, that branch (with its accessibility relation) is a modal Hintikka set, provided the
bundled loop invariant `ModalLoopInv` (above) holds for every branch/expanded-set/`acc` triple
in the initial worklist under *some* per-index rank map, and the worklist's `modalExpMeasure` is
bounded by the available fuel.

Proved by induction on `fuel`, mirroring `classicalExpandBranches_hintikka`
(`Classical/Completeness.lean:924`): the `fuel = 0` case is vacuous (the measure bound forces
`branches = []`, so `modalExpandBranches`'s fuel-exhausted lookup returns `.closed`, never
`.openBranch`); the `fuel = n + 1` case is an inner induction on the `processNext` worklist,
mirroring `modalExpandBranches_closed_unsat`'s three-parallel-list threading
(`Soundness.lean:164`) with an additional `ModalLoopInv`-existence hypothesis at every index.
A `modalStepBranch = none` saturated leaf is closed via `modalStepBranch_none_saturated`
(each `sf ∈ b` is either in `e` — where `ModalLoopInv.hintikkaInv`/`.eBoxOnlyNeg` discharge
`modalHintikkaSet`'s second conjunct — or has `modalApplyOne`-result `notApplicable`, discharging
it directly) and `ModalLoopInv.eBoxNegWitness` (third conjunct, using that `boxNeg` is always
applicable so a saturated `F(□ψ)@w` is necessarily in `e`). An expansion step advances via
`modalStep_preserves_invariant` (P5a) for the invariant and `modalExpMeasure_step_lt` for the
measure bound, splitting the new worklist's indices into the unchanged `done`/`bt` regions and
the freshly-produced `newBs` region (all sharing the single constant expanded-set `newExp` and
accessibility relation `newAcc`, `modalStepBranch_newExps_const`).

Byte-identical-statement corollary of `modalExpandBranchesGen_hintikka` (the crux) via
`modalExpandBranches_eq`/`modalHintikkaSet_eq`/`ModalLoopInv_iff_gen`. -/
lemma modalExpandBranches_hintikka (φ0 : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      modalExpMeasure (modalUniverse φ0) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        ∃ rank, ModalLoopInv φ0 bi ei ai rank) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranches branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSet bR aR := by
  intro branches expandedSets accs hlen hlenA hfuel hInv bR aR h
  have hInv' : ∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
      (ai : Accessibility),
      branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
      ∃ rank, ModalLoopInvGen modalApplyOne φ0 bi ei ai rank := by
    intro i bi ei ai hib hie hia
    obtain ⟨rank, hinv⟩ := hInv i bi ei ai hib hie hia
    exact ⟨rank, (ModalLoopInv_iff_gen φ0 bi ei ai rank).mp hinv⟩
  rw [modalExpandBranches_eq] at h
  rw [modalHintikkaSet_eq]
  exact modalExpandBranchesGen_hintikka modalApplyOne φ0 (modalApplyOne_spec.toAt φ0) fuel branches
    expandedSets accs hlen hlenA hfuel hInv' bR aR h

/-! ## Initial-Branch Membership Persistence -/

/-- One `modalStepBranch` step preserves membership of a fixed formula `sf` already on the
branch: mirrors `modalLoop_bClosure`'s case split (every child branch is `newForms ++ b` or
`br ++ b` for some `br`/`newForms`, so any pre-existing branch member survives via
`List.mem_append_right`). -/
private lemma modalStepBranchGen_mem_preserved
    (apply : RuleApply Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsf : sf ∈ b)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc)) :
    ∀ b' ∈ newBs, sf ∈ b' := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, hsfmem, hsf'⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf' with hexp
  rcases hfstc : (apply sf_exp b acc).fst with nf | brs | nf | _
  · rw [hfstc] at hsf'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf'
    intro b' hb'
    rw [← hsf'.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact List.mem_append_right _ hsf
  · rw [hfstc] at hsf'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf'
    intro b' hb'
    rw [← hsf'.1] at hb'
    obtain ⟨br, -, rfl⟩ := List.mem_map.mp hb'
    exact List.mem_append_right _ hsf
  · rw [hfstc] at hsf'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf'
    intro b' hb'
    rw [← hsf'.1] at hb'
    simp only [List.mem_singleton] at hb'
    subst hb'
    exact List.mem_append_right _ hsf
  · rw [hfstc] at hsf'; simp at hsf'

/-- Every `modalStepBranch` step preserves membership of a fixed formula `sf` already on the
branch: mirrors `modalLoop_bClosure`'s case split (every child branch is `newForms ++ b` or
`br ++ b` for some `br`/`newForms`, so any pre-existing branch member survives via
`List.mem_append_right`).

Byte-identical-statement corollary of `modalStepBranchGen_mem_preserved` via
`modalStepBranch_eq`. -/
private lemma modalStepBranch_mem_preserved
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsf : sf ∈ b)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc)) :
    ∀ b' ∈ newBs, sf ∈ b' :=
  modalStepBranchGen_mem_preserved modalApplyOne b e acc sf hsf newBs newExps newAcc
    (modalStepBranch_eq b e acc ▸ hstep)

/-- **Generic initial-branch membership persistence**: `modalExpandBranchesGen_
openBranch_initial_mem`, over an abstract `apply`. Takes **no** field -- driver-structural, needed
by the T system for its own truth lemma. Not `private`: the proof is genuinely
`apply`-agnostic (never inspects `apply`'s output shape), so `modalTableauT_complete`
(`FrameCompleteness.lean`) reuses it directly at `apply := modalApplyOneT` rather than
re-deriving an identical T-specific copy. -/
lemma modalExpandBranchesGen_openBranch_initial_mem
    (apply : RuleApply Atom) (fuel : Nat)
    (sf : SignedFormula (Proposition Atom) WorldIndex) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ b₀ ∈ branches, sf ∈ b₀) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
        sf ∈ bR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs _hlen _hlenA hAll bR aR h
    simp only [modalExpandBranchesGen] at h
    cases hfs : (branches.zip accs).findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | none => simp only [hfs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨pb, pa⟩ := p
      simp only [hfs] at h
      injection h with hp1 hp2
      obtain ⟨q, hqmem, hf⟩ := List.exists_of_findSome?_eq_some hfs
      obtain ⟨qb, qa⟩ := q
      simp only [] at hf
      by_cases hcl : isModalClosed qb = true
      · rw [if_pos hcl] at hf
        exact absurd hf (by simp)
      · rw [if_neg hcl] at hf
        have hq0mem : qb ∈ branches := (List.of_mem_zip hqmem).1
        have hqp : (qb, qa) = (pb, pa) := Option.some.inj hf
        have hqfst : qb = bR := by
          have : qb = pb := congrArg Prod.fst hqp
          rw [this]; exact hp1
        rw [hqfst] at hq0mem
        exact hAll bR hq0mem
  | succ fuel' ih =>
    intro branches expandedSets accs hlen hlenA hAll bR aR h
    simp only [modalExpandBranchesGen] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        (∀ bp ∈ pending, sf ∈ bp) →
        (∀ bd ∈ done, sf ∈ bd) →
        modalExpandBranchesGen.processNext apply fuel' pending pendingExp pendingAccs done doneExp
            doneAccs = .openBranch bR aR →
        sf ∈ bR from
      key branches expandedSets accs [] [] [] hlen hlenA rfl rfl hAll (by simp)
        (by simpa [modalExpandBranchesGen] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs done doneExp doneAccs _ _ _ _ _ _ hinner
      simp [modalExpandBranchesGen.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs done doneExp doneAccs
        hlength_p hlenP_accs hdlength hdAccs hAll_p hAll_d hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength_p hlenP_accs
          simp only [modalExpandBranchesGen.processNext] at hinner
          by_cases hcl : isModalClosed bh = true
          · rw [if_pos hcl] at hinner
            have hAll_bt : ∀ bp ∈ bt, sf ∈ bp := fun bp hbp => hAll_p bp (by simp [hbp])
            have hAll_done_bh : ∀ bd ∈ done ++ [bh], sf ∈ bd := by
              intro bd hbd
              simp only [List.mem_append, List.mem_singleton] at hbd
              rcases hbd with hd | heq
              · exact hAll_d bd hd
              · subst heq; exact hAll_p bd (by simp)
            exact ih_inner es restAs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
              hlength_p hlenP_accs (by simp [hdlength]) (by simp [hdAccs])
              hAll_bt hAll_done_bh hinner
          · simp only [Bool.not_eq_true] at hcl
            rw [if_neg (by simp [hcl])] at hinner
            cases hstep : modalStepBranchGen apply bh e a with
            | none =>
              rw [hstep] at hinner
              have hbeq : bh = bR ∧ a = aR := by cases hinner; exact ⟨rfl, rfl⟩
              exact hbeq.1 ▸ hAll_p bh (by simp)
            | some step =>
              obtain ⟨newBs, newExps, newAcc⟩ := step
              rw [hstep] at hinner
              have hbh_sf : sf ∈ bh := hAll_p bh (by simp)
              have hNewBs_sf : ∀ b' ∈ newBs, sf ∈ b' :=
                modalStepBranchGen_mem_preserved apply bh e a sf hbh_sf newBs newExps newAcc hstep
              have hLenNBE : newExps.length = newBs.length := by
                obtain ⟨newExp, hEq⟩ :=
                  modalStepBranchGen_newExps_const apply bh e a newBs newExps newAcc hstep
                simp [hEq]
              exact ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                (by simp [hdlength, hlength_p, hLenNBE])
                (by simp [hdAccs, hlenP_accs])
                (fun b' hb'_mem => by
                  simp only [List.mem_append] at hb'_mem
                  rcases hb'_mem with (hd | hn) | hbt
                  · exact hAll_d b' hd
                  · exact hNewBs_sf b' hn
                  · exact hAll_p b' (by simp [hbt]))
                bR aR hinner

/-- Every formula in every initial branch appears in the open branch returned by
`modalExpandBranches`. Mirrors the classical propositional tableau's
`classicalExpandBranches_openBranch_initial_mem`
(`Classical/Completeness.lean:1164`), extended with the per-branch `acc` parallel list. Used to
show `F(φ0)@0` is on the countermodel branch.

Byte-identical-statement corollary of `modalExpandBranchesGen_openBranch_initial_mem`
via `modalExpandBranches_eq`. -/
private lemma modalExpandBranches_openBranch_initial_mem (fuel : Nat)
    (sf : SignedFormula (Proposition Atom) WorldIndex) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ b₀ ∈ branches, sf ∈ b₀) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranches branches expandedSets accs fuel = .openBranch bR aR →
        sf ∈ bR := by
  intro branches expandedSets accs hlen hlenA hAll bR aR h
  rw [modalExpandBranches_eq] at h
  exact modalExpandBranchesGen_openBranch_initial_mem modalApplyOne fuel sf branches expandedSets
    accs hlen hlenA hAll bR aR h

/-! ## Initial Loop Invariant and the Public Completeness/Decidability Results -/

/-- **Generic initial-configuration loop invariant**: `modalLoopInvGen_initial`, over
an abstract `apply`. Takes **no** field -- the five rule-dependent conjuncts are all vacuous over
`e = []`, so nothing about `apply` is ever consulted. Not `private`: reused
directly at `apply := modalApplyOneT` by `modalTableauT_complete` (`FrameCompleteness.lean`). -/
lemma modalLoopInvGen_initial (apply : RuleApply Atom) (φ0 : Proposition Atom) :
    ModalLoopInvGen apply φ0
      [(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      Accessibility.empty (fun _ => modalDepth φ0) := by
  have hmemU : (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalUniverse φ0 := by
    have hw : (0 : WorldIndex) < modalWorldBound φ0 + 1 := Nat.succ_pos _
    simp only [modalUniverse, List.mem_flatMap, List.mem_range]
    exact ⟨0, hw, φ0, modalSubfmls_self_mem φ0, by simp⟩
  have hmax : modalMaxWorld [(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] = 0 :=
    by simp [modalMaxWorld]
  have houtdeg0 : ∀ w : WorldIndex, outDeg Accessibility.empty w = 0 := fun w => rfl
  refine ⟨⟨?_, List.nodup_nil, ?_, accFreshInv_empty _, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hmemU
  · intro x hx
    simp at hx
  · intro w w' hedge
    simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
    exact absurd hedge (by decide)
  · intro w
    rw [houtdeg0 w]
    simp
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact Nat.le_refl (modalDepth φ0)
  · intro w w' hedge
    simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
    exact absurd hedge (by decide)
  · -- phiBound
    have hpotEq : modalPotential (modalSubfmls φ0).length
        [(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]
        Accessibility.empty (fun _ => modalDepth φ0) =
        modalPotentialTerm (modalSubfmls φ0).length Accessibility.empty
          (fun _ => modalDepth φ0) 0 := by
      simp [modalPotential, modalKnownWorlds]
    have hterm : modalPotentialTerm (modalSubfmls φ0).length Accessibility.empty
        (fun _ => modalDepth φ0) 0 + 1 = geomCap (modalSubfmls φ0).length (modalDepth φ0) := by
      unfold modalPotentialTerm
      simp only []
      rcases hd : modalDepth φ0 with _ | k
      · simp
      · rw [if_neg (by omega), houtdeg0 0]
        simp only [Nat.sub_zero, Nat.add_sub_cancel]
        rw [geomCap_succ]
        omega
    rw [hmax, hpotEq]
    have hbound : 0 + modalPotentialTerm (modalSubfmls φ0).length Accessibility.empty
        (fun _ => modalDepth φ0) 0 + 1 ≤
        modalPotentialTerm (modalSubfmls φ0).length Accessibility.empty
          (fun _ => modalDepth φ0) 0 + 1 := by omega
    exact hterm ▸ hbound
  · intro sf hsf
    simp at hsf
  · intro sf hsf
    simp at hsf
  · intro sf hsf
    simp at hsf
  · intro sf hsf
    simp at hsf
  · intro sf hsf
    simp at hsf

/-- The bundled loop invariant `ModalLoopInv` holds at the tableau's initial configuration:
branch `[F(φ0)@0]`, empty expanded set, empty accessibility relation, and the constant rank
map `fun _ => modalDepth φ0`. Every `ModalPotentialInv` field is either a direct computation
(`bClosure`, `rankBound`) or vacuous over `e = []`/`acc = Accessibility.empty`
(`eNodup`, `eClosure`, `accKnown`, `outDegEq`, `rankEdge`, and `ModalLoopInv`'s own
`hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`, all quantified over `e = []`); `phiBound` is an
exact equality driven by `geomCap`'s defining recursion (`geomCap_succ`), not merely a bound.

Byte-identical-statement corollary of `modalLoopInvGen_initial` via
`ModalLoopInv_iff_gen`. -/
private lemma modalLoopInv_initial (φ0 : Proposition Atom) :
    ModalLoopInv φ0 [(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      Accessibility.empty (fun _ => modalDepth φ0) :=
  (ModalLoopInv_iff_gen φ0 _ _ _ _).mpr (modalLoopInvGen_initial modalApplyOne φ0)

/-- **K-completeness of the modal tableau**: if the tableau on `φ0`
returns an open branch, `φ0` is not K-valid. Combines the top-loop Hintikka lemma
(`modalExpandBranches_hintikka`, above) instantiated at the initial configuration (via
`modalLoopInv_initial` and the fuel bridge `modalExpMeasure_entry_le_fuel`), the initial-branch
membership persistence lemma (`modalExpandBranches_openBranch_initial_mem`, above) showing
`F(φ0)@0` survives to the returned branch, and the countermodel extraction theorem
(`modalOpenBranch_countermodel`, `Completeness.lean:561`). -/
theorem modalTableau_complete (φ0 : Proposition Atom)
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {a : Accessibility}
    (h : modalTableau φ0 = .openBranch b a) :
    ¬ kValid φ0 := by
  have h' : modalExpandBranches
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      [Accessibility.empty] (modalFuel φ0) = .openBranch b a := by
    simpa only [modalTableau] using h
  have hmeas := modalExpMeasure_entry_le_fuel φ0
  have hInv : ∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
      (ai : Accessibility),
      ([[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]])[i]? = some bi →
      (([[]] : List (List (SignedFormula (Proposition Atom) WorldIndex))))[i]? = some ei →
      ([Accessibility.empty])[i]? = some ai →
      ∃ rank, ModalLoopInv φ0 bi ei ai rank := by
    intro i bi ei ai hib hie hia
    match i with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
      subst hib; subst hie; subst hia
      exact ⟨fun _ => modalDepth φ0, modalLoopInv_initial φ0⟩
    | n + 1 => simp at hib
  have hH : modalHintikkaSet b a :=
    modalExpandBranches_hintikka φ0 (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl hmeas hInv b a h'
  have hmemInit : (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    modalExpandBranches_openBranch_initial_mem (modalFuel φ0)
      (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (fun b₀ hb₀ => by
        simp only [List.mem_singleton] at hb₀
        subst hb₀
        simp)
      b a h'
  have hnot := modalOpenBranch_countermodel b a φ0 hH hmemInit
  intro hkv
  exact hnot (hkv WorldIndex (extractModel b a) 0)

/-- **The modal K tableau decides K-validity**: `modalTableau φ0`
closes exactly when `φ0` is K-valid. Combines soundness (`modalTableau_sound`,
`Soundness.lean:334`) with completeness (`modalTableau_complete`, above) via the two-constructor
dichotomy of `ModalTableauResult`. -/
theorem modalTableau_decides (φ0 : Proposition Atom) :
    modalTableau φ0 = .closed ↔ kValid φ0 := by
  constructor
  · exact modalTableau_sound φ0
  · intro hkv
    cases htab : modalTableau φ0 with
    | closed => rfl
    | openBranch b a => exact absurd hkv (modalTableau_complete φ0 htab)

/-- **K-validity is decidable**: decide by running the modal K
tableau and consulting `modalTableau_decides`. No `Fintype Atom` assumption is needed, since the
tableau computation itself is the decision procedure. -/
instance instDecidableKValid (φ0 : Proposition Atom) : Decidable (kValid φ0) :=
  match h : modalTableau φ0 with
  | .closed => .isTrue ((modalTableau_decides φ0).mp h)
  | .openBranch _ _ => .isFalse (modalTableau_complete φ0 h)

end Cslib.Logic.Modal.Tableau

end
