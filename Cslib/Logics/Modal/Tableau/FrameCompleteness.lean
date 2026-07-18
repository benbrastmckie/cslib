/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Completeness
public import Cslib.Logics.Modal.Tableau.LoopChecking
public import Cslib.Logics.Modal.Tableau.FrameSoundness
public import Cslib.Logics.Modal.Tableau.TDriver
public import Cslib.Logics.Modal.Tableau.BDriver
public import Cslib.Foundations.Relation.Euclidean

/-! # Frame-Relativized Modal Tableau Completeness (Shared Extractor Skeleton)

This module fixes the shared **closure-at-extraction** helper used by every frame-specific
completeness proof (T, S4, S5, B, 5): given an open saturated branch `b` and accessibility
relation `acc`, extract a Kripke model whose relation is a *closure* `Cl acc.hasEdge` of the
raw tableau accessibility relation, rather than `acc.hasEdge` itself (as `extractModel` does
for K, `Completeness.lean:59`).

## Strategy (Strategy B, closure-at-extraction)

Per-system phases instantiate `Cl` with a Mathlib closure operator so the frame-condition
instance comes free:

| System | Closure operator `Cl` | Frame instance (free) |
|--------|------------------------|------------------------|
| T      | `Relation.ReflGen`     | `Std.Refl` |
| S4     | `Relation.ReflTransGen`| `Std.Refl`, `IsTrans` |
| B      | `Relation.SymmGen`     | `Std.Symm` |
| S5     | universal (`fun _ _ => True`) or `Relation.EqvGen` | `IsEquiv` |

No new frame predicates are defined here — the per-system files reuse the `Cube.lean` frame
classes (`Std.Refl`, `IsTrans`, `Std.Symm`, `Relation.RightEuclidean`) and the
`Satisfies.t`/`Satisfies.b`/`Satisfies.four`/`Satisfies.five` semantic validity theorems for
their soundness arms.

## Main Definitions

- `extractModelWith`: parameterized model extractor over a closure operator `Cl`, mirroring
  `extractModel` (`Completeness.lean:59`) but with `r := Cl acc.hasEdge` instead of
  `r := acc.hasEdge`. The valuation clause is preserved verbatim.

## Notes

This file intentionally does **not** commit to a truth lemma or Hintikka-set characterization:
those are frame-specific (each system's saturation rules determine what Hintikka property the
open branch enjoys, hence what the truth lemma needs to bridge across the closure's extra
edges). Per-system phases add their own `extractModel{T,S4,B,...}` (specialized instances of
`extractModelWith`) and truth lemmas in `FrameCompleteness.lean` / their own dedicated file
(`S5Simplification.lean`, `LoopChecking.lean`), reusing this module's docstring conventions.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v
variable {Atom : Type v} [DecidableEq Atom] [Hashable Atom]

/-! ## Shared Closure-at-Extraction Helper -/

/-- Extract a Kripke model from an open saturated branch `b` and accessibility relation `acc`,
using the closure `Cl acc.hasEdge` as the model's relation instead of `acc.hasEdge` itself
(Strategy B, closure-at-extraction). The world type is `WorldIndex` (= `Nat`), matching
`extractModel` (`Completeness.lean:59`); the valuation clause is preserved verbatim: atom `p`
holds at world `w` iff `T(atom p)@w ∈ b`.

Per-system phases instantiate `Cl` with a Mathlib closure operator
(`Relation.ReflGen`/`ReflTransGen`/`SymmGen`, or the universal relation for S5) so that the
frame-condition instance (`Std.Refl`, `IsTrans`, `Std.Symm`, `IsEquiv`) comes free off the
closure operator — see the module docstring table. -/
def extractModelWith
    (Cl : (WorldIndex → WorldIndex → Prop) → (WorldIndex → WorldIndex → Prop))
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom where
  r := Cl (fun w w' => acc.hasEdge w w' = true)
  v w p := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true

omit [Hashable Atom] in
/-- `extractModelWith` with the identity closure operator is exactly `extractModel` (K). -/
lemma extractModelWith_id (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    extractModelWith (Atom := Atom) id b acc = extractModel b acc := rfl

/-! ## T (Reflexive Frame) Extraction -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*reflexive closure* `Relation.ReflGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.ReflGen`). The frame instance
`Std.Refl` comes free off `Relation.reflexive_reflGen` (see `extractModelT_refl` below); no
new frame predicate is defined. -/
def extractModelT
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.ReflGen) b acc

omit [Hashable Atom] in
/-- `extractModelT`'s relation is exactly the reflexive closure of `acc.hasEdge`. -/
lemma extractModelT_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelT b acc).r = Relation.ReflGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- The reflexive frame condition holds of `extractModelT b acc` "for free": `Relation.ReflGen`
is always reflexive (`Relation.reflexive_reflGen`), regardless of the underlying raw edge
relation `acc.hasEdge`. Discharges the `reflFC` witness (`FrameSoundness.lean`) for the T
countermodel. -/
lemma extractModelT_refl (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Refl (extractModelT b acc).r := by
  rw [extractModelT_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelT`'s
(reflexive-closure) relation via `Relation.ReflGen.single`. Needed to reuse the K bridge
lemmas (`hintikka_box_pos`, `hintikka_diamond_pos`, etc.), which are stated in terms of
`acc.hasEdge`, when relating them to `extractModelT`'s closed relation. -/
lemma extractModelT_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelT b acc).r w w' := by
  rw [extractModelT_r]
  exact Relation.ReflGen.single h

/-! ## S4 (Reflexive-Transitive Frame) Extraction -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*reflexive-transitive closure* `Relation.ReflTransGen` of `acc.hasEdge` as the model's relation
(Strategy B, closure-at-extraction, instantiated with `Cl := Relation.ReflTransGen`). Both the
`Std.Refl` and `IsTrans` frame instances come free off `Relation.ReflTransGen`
(`extractModelS4_refl`, `extractModelS4_trans` below); no new frame predicate is defined. -/
def extractModelS4
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.ReflTransGen) b acc

omit [Hashable Atom] in
/-- `extractModelS4`'s relation is exactly the reflexive-transitive closure of `acc.hasEdge`. -/
lemma extractModelS4_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelS4 b acc).r =
      Relation.ReflTransGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- The reflexive frame condition holds of `extractModelS4 b acc` "for free":
`Relation.ReflTransGen` is always reflexive (`Relation.reflexive_reflTransGen`), regardless of
the underlying raw edge relation `acc.hasEdge`. Discharges half of the `s4FC` witness
(`FrameSoundness.lean`) for the S4 countermodel. -/
lemma extractModelS4_refl (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Refl (extractModelS4 b acc).r := by
  rw [extractModelS4_r]
  infer_instance

omit [Hashable Atom] in
/-- The transitive frame condition holds of `extractModelS4 b acc` "for free":
`Relation.ReflTransGen` is always transitive (`Relation.transitive_reflTransGen`), regardless
of the underlying raw edge relation `acc.hasEdge`. Discharges the other half of the `s4FC`
witness (`FrameSoundness.lean`) for the S4 countermodel. Note this is Mathlib's `IsTrans`
class (matching the `Cube.lean` spelling of S4's transitivity), while `extractModelT_refl`
above uses `Std.Refl` -- the two frame instances have different (mixed) provenance in
Mathlib, and both are picked up here unchanged. -/
lemma extractModelS4_trans (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    IsTrans WorldIndex (extractModelS4 b acc).r := by
  rw [extractModelS4_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelS4`'s
(reflexive-transitive-closure) relation via `Relation.ReflTransGen.single`. Needed to lift the
S4 bridge lemmas' single-edge hypotheses (`LoopChecking.lean`) into the closure whenever a raw
edge (rather than a whole `ReflTransGen` path) is at hand. -/
lemma extractModelS4_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelS4 b acc).r w w' := by
  rw [extractModelS4_r]
  exact Relation.ReflTransGen.single h

/-! ## S4 Modal Truth Lemma -/

/-- `modalApplyOneS4 φ₀` agrees with the plain K dispatch `modalApplyOne` on every
non-modal-shaped signed formula (i.e. neither `box`- nor `diamond`-shaped, regardless of
sign): none of the guard's two minting shapes (`F(□·)`, `T(◇·)`) or the 4-rule/T-self
shapes (`T(□·)`, `F(◇·)`) apply, so the three-layer dispatch
(`modalApplyOneS4` → `modalApplyOneS4Rules` → `modalApplyOneT` → `modalApplyOne`) collapses
via `modalApplyOneS4_eq_of_not_boxNeg_diaPos`, `modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg`,
and `modalApplyOneT_eq_of_not_boxPos_diaNeg` chained together. This is exactly what lets the
S4 truth lemma's propositional cases (`imp`/`and`/`or`/`atom`/`bot`) reuse K's
`modalApplyOne_imp_pos` etc. bridge lemmas verbatim. -/
private lemma modalApplyOneS4_eq_of_not_modal_shaped
    (φ₀ : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    modalApplyOneS4 φ₀ sf b acc = modalApplyOne sf b acc := by
  have hguard : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩
  have hfour : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
      ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩
  rw [modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hguard,
    modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hfour,
    modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hfour]

/-- Modal Truth Lemma for S4: membership in an S4 Hintikka branch tracks satisfaction in the
extracted reflexive-transitive Kripke model `extractModelS4 b acc`.

For every formula `φ` and world `w`, `T(φ)@w ∈ b` implies `φ` is satisfied at `w` in
`extractModelS4 b acc`, and `F(φ)@w ∈ b` implies it is not. Proof by strong induction on
`modalComplexity φ`, mirroring `modalTruthLemma` (`Completeness.lean`): the propositional
cases (`atom`/`bot`/`imp`/`and`/`or`) reuse the public, apply-agnostic consistency kit
(`openBranch_noTBot`/`openBranch_noContradiction`) and K's `modalApplyOne_*` bridge lemmas
verbatim, routed through `modalApplyOneS4_eq_of_not_modal_shaped`; the box/diamond cases
consume the S4-specific `hintikkaS4_box_pos_reflTransGen`/`hintikkaS4_box_neg`/
`hintikkaS4_diamond_pos`/`hintikkaS4_dia_neg_reflTransGen` bridges (`LoopChecking.lean`),
with the model's `r w w'` unfolding to exactly the `ReflTransGen` hypothesis those bridges
want (`extractModelS4_r`). This is a genuinely new induction, not a reuse of
`modalTruthLemma`: that lemma is pinned to `extractModel` (`r := acc.hasEdge`), whereas
`extractModelS4`'s `r` is the reflexive-transitive closure -- different propositions. -/
lemma modalTruthLemmaS4
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS4 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS4 b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS4 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS4 b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelS4 b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelS4 b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelS4, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelS4, extractModelWith, List.any_eq_true] at hsat
        obtain ⟨sf, hsf_mem, hcond⟩ := hsat
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
        have hsign_eq : sf.sign = .pos := eq_of_beq hsign
        have hform_eq : sf.formula = .atom p := eq_of_beq hform
        have hlab_eq : sf.label = w := eq_of_beq hlab
        have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
          convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
        exact openBranch_noContradiction b hHopen (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hHopen w), ?_⟩
      intro _ hsat
      exact hsat
    | imp a c =>
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hHrule ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS4_eq_of_not_modal_shaped φ₀ _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        have hpath : Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelS4_r b acc ▸ hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaS4_box_pos_reflTransGen φ₀ b acc hH ψ w w' hmem hpath)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikkaS4_box_neg φ₀ b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelS4_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikkaS4_diamond_pos φ₀ b acc hH ψ w hmem
        exact ⟨w', extractModelS4_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelS4_r b acc ▸ hw'
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaS4_dia_neg_reflTransGen φ₀ b acc hH ψ w w' hmem hpath) hsψ

/-- An open S4 Hintikka branch with `F(φ₀)@0 ∈ b` yields a reflexive-transitive Kripke
countermodel to `φ₀`. The extracted model `extractModelS4 b acc` falsifies `φ₀` at world
`0`, and its relation satisfies `s4FC` "for free" (`extractModelS4_refl`/
`extractModelS4_trans`, both discharged with no manual frame reasoning). Mirrors
`modalOpenBranch_countermodel` (`Completeness.lean`). -/
theorem modalOpenBranchS4_countermodel
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (hH : modalHintikkaSetS4 φ₀ b acc)
    (hF : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (¬ Satisfies (extractModelS4 b acc) 0 φ₀) ∧ s4FC (extractModelS4 b acc).r :=
  ⟨(modalTruthLemmaS4 φ₀ b acc hH φ₀ 0).2 hF,
    ⟨extractModelS4_refl b acc, extractModelS4_trans b acc⟩⟩

/-! ## B (Symmetric Frame) Extraction (task 505 Phase 5)

Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*symmetric closure* `Relation.SymmGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.SymmGen`). The frame instance
`Std.Symm` comes free off `Relation.SymmGen`'s own unnamed `instance : Std.Symm (SymmGen r)`
(`Mathlib.Logic.Relation`); no new frame predicate is defined. Unlike `Relation.ReflGen`/
`Relation.ReflTransGen` (inductive types with named constructors `.refl`/`.single`/`.tail`),
`Relation.SymmGen r a b` is literally `r a b ∨ r b a` (a `def`, not an inductive), so case
analysis on a `SymmGen` hypothesis is a plain `Or` split -- the forward direction reduces to
K's own successor argument, the backward direction to B's own predecessor argument
(`hintikkaB_box_pos`/`hintikkaB_diamond_neg`, Phase 6 below). -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*symmetric closure* `Relation.SymmGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.SymmGen`). -/
def extractModelB
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.SymmGen) b acc

omit [Hashable Atom] in
/-- `extractModelB`'s relation is exactly the symmetric closure of `acc.hasEdge`. -/
lemma extractModelB_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelB b acc).r = Relation.SymmGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- The symmetric frame condition holds of `extractModelB b acc` "for free": `Relation.SymmGen`
is always symmetric (its own unnamed `instance : Std.Symm (SymmGen r)`, `Mathlib.Logic.
Relation`), regardless of the underlying raw edge relation `acc.hasEdge`. Discharges the
`symmFC` witness (`FrameSoundness.lean`) for the B countermodel. -/
lemma extractModelB_symm (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Symm (extractModelB b acc).r := by
  rw [extractModelB_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelB`'s
(symmetric-closure) relation via `Relation.SymmGen.of_rel` (`Or.inl`). Needed to reuse the K
bridge lemmas (`hintikka_box_neg`, `hintikka_diamond_pos`, etc.), which are stated in terms of
`acc.hasEdge`, when relating them to `extractModelB`'s closed relation. -/
lemma extractModelB_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelB b acc).r w w' := by
  rw [extractModelB_r]
  exact Relation.SymmGen.of_rel h

omit [Hashable Atom] in
/-- The *backward* direction survives into `extractModelB`'s relation too, via
`Relation.SymmGen.of_rel_symm` (`Or.inr`): a raw edge `v → w` (`acc.hasEdge v w`) gives
`(extractModelB b acc).r w v` (the reversed pair) directly -- the symmetric-closure analogue of
`extractModelB_hasEdge_imp_r` for the predecessor direction B's own rule reads. -/
lemma extractModelB_hasEdge_symm_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {v w : WorldIndex} (h : acc.hasEdge v w = true) :
    (extractModelB b acc).r w v := by
  rw [extractModelB_r]
  exact Relation.SymmGen.of_rel_symm h

/-! ## S5 (Equivalence Frame) Extraction (task 504 Phase 3)

Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*equivalence closure* `Relation.EqvGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.EqvGen`). This extraction is
**independent of the tableau rule** -- a pure closure-model construction over any branch/
accessibility pair -- and is delivered here regardless of Phase 2's blocked status (see
`S5Simplification.lean`'s "Phase 2 Obstruction" section).

**Correction against the plan**: the plan cites `Relation.EqvGen.instIsEquiv`, but no such
instance exists in Mathlib (confirmed: `infer_instance` fails for
`IsEquiv _ (Relation.EqvGen r)`; only `Relation.EqvGen.is_equivalence : Equivalence (EqvGen r)`
and the individual constructors `.refl`/`.symm`/`.trans` are provided). `instIsEquivEqvGen`
below builds the instance directly from those constructors -- three one-line proofs, no new
mathematical content, exactly the "for free off Mathlib" claim the plan makes, just assembled by
hand rather than found pre-packaged. -/

/-- `IsEquiv` for `Relation.EqvGen`: built directly from the closure's own constructors
(`.refl`/`.symm`/`.trans`), since Mathlib ships no unconditional instance for this combination
(unlike `Relation.SymmGen`'s `Std.Symm` instance, reused verbatim by `extractModelB_symm` above).
Generic over any type/relation, not modal-tableau-specific; kept in this namespace since it is
needed only here. -/
instance instIsEquivEqvGen {α : Type*} (r : α → α → Prop) : IsEquiv α (Relation.EqvGen r) where
  refl := Relation.EqvGen.refl
  trans := fun _ _ _ h1 h2 => Relation.EqvGen.trans _ _ _ h1 h2
  symm := fun _ _ h => Relation.EqvGen.symm _ _ h

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*equivalence closure* `Relation.EqvGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.EqvGen`). -/
def extractModelS5
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.EqvGen) b acc

omit [Hashable Atom] in
/-- `extractModelS5`'s relation is exactly the equivalence closure of `acc.hasEdge`. -/
lemma extractModelS5_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelS5 b acc).r = Relation.EqvGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- The equivalence frame condition holds of `extractModelS5 b acc` "for free": `Relation.EqvGen`
is always an equivalence relation (`instIsEquivEqvGen` above), regardless of the underlying raw
edge relation `acc.hasEdge`. Discharges the `s5FC` witness (`FrameSoundness.lean`) for the S5
countermodel; its `Std.Refl`/`Std.Symm`/`IsTrans` projections are obtained downstream via
`IsEquiv`'s own field projections. -/
lemma extractModelS5_equiv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    IsEquiv WorldIndex (extractModelS5 b acc).r := by
  rw [extractModelS5_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelS5`'s
(equivalence-closure) relation via `Relation.EqvGen.rel`. Needed to reuse the K bridge lemmas
(`hintikka_box_neg`, `hintikka_diamond_pos`, etc.), which are stated in terms of `acc.hasEdge`,
when relating them to `extractModelS5`'s closed relation. -/
lemma extractModelS5_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelS5 b acc).r w w' := by
  rw [extractModelS5_r]
  exact Relation.EqvGen.rel _ _ h

omit [Hashable Atom] in
/-- Every known world of `b` is `extractModelS5`-related to every other known world of `b`,
*provided* both are connected to a common recorded-edge chain -- in particular, `Relation.EqvGen`
being symmetric+transitive means any two worlds reachable from a shared ancestor via raw edges
are related, regardless of direction. Stated here as the reflexivity instance specialized to a
single world (the trivial case of the cluster property: every world is related to itself),
since the general "any two known worlds are related" fact requires connectivity of the
underlying tree (established per-branch, not by the extractor alone). -/
lemma extractModelS5_refl (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) :
    (extractModelS5 b acc).r w w :=
  Relation.EqvGen.refl w

omit [Hashable Atom] in
/-- `extractModelS5`'s relation satisfies `Relation.RightEuclidean`, obtained directly from
`IsEquiv`'s `symm` + `trans` projections: `r a b → r a c → r b c` follows by symmetry (`r a b`
gives `r b a`) then transitivity (`r b a` with `r a c` gives `r b c`). This is the free 5/KB5
(Euclidean) exposure the plan's Phase 7 targets -- delivered here since it depends only on
`extractModelS5_equiv` (Phase 3), independent of the blocked Phase 2 rule discharge. There is
**no** `RightEuclidean.symm` lemma (confirmed against `Defs.lean:49`); the plan's documented
alternative route via `Relation.symm_rightEuclidean_iff_trans`
(`Cslib/Foundations/Relation/Euclidean.lean:236`) requires a `[Std.Symm r]` instance that is not
available generically for `Relation.EqvGen`, so this lemma instead builds the `RightEuclidean`
witness directly from `IsEquiv`'s own `symm`/`trans` fields (both routes are mathematically
equivalent; the direct route avoids an extra typeclass search). -/
lemma extractModelS5_rightEuclidean (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Relation.RightEuclidean (extractModelS5 b acc).r := by
  have hequiv := extractModelS5_equiv b acc
  exact ⟨fun hab hac => hequiv.trans _ _ _ (hequiv.symm _ _ hab) hac⟩

/-! ## 5 / KB5 (Euclidean) Coverage via the S5 Route: Status (task 504 Phase 7)

`extractModelS5_rightEuclidean` above delivers the free Euclidean exposure the plan's Phase 7
targets: `Relation.RightEuclidean (extractModelS5 b acc).r` holds unconditionally, since every
equivalence relation is right-Euclidean. This is genuinely independent of Phase 2 (it only needs
`extractModelS5_equiv`, a Phase 3 result).

**CORRECTED (this docstring previously framed the gap below as a SCHEDULING dependency --
*"needs `modalTableauS5_complete`/`modalTableauS5_sound` as its proof engine, both transitively
blocked by Phase 2"* -- which is wrong on the mathematics and misled a prior planning cycle into
attempting a route that provably cannot arrive).**

**What is actually true: 5/KB5 is not deliverable *via the S5 tableau route*, at all, regardless
of whether `modalTableauS5_complete`/`modalTableauS5_sound` exist.** This is a **frame-class
inclusion obstruction**, proven (not argued) by
`specs/515_s5_universal_rule_termination_unblock_504/probes/five-s5-separation.lean`
(sorry-free, **zero axioms**): `s5FC = Std.Refl r ∧ Relation.RightEuclidean r`
(`FrameSoundness.lean:1273`), but `fiveFC = Relation.RightEuclidean r` **alone** (:1282,
reflexivity absent) and `kb5FC = Std.Symm r ∧ Relation.RightEuclidean r` (:1291, reflexivity
absent) are **strictly larger** frame classes. `□p → p` on the one-world **empty** frame
separates them: `RightEuclidean` and `Std.Symm` are both vacuous with no edges, so `□p` holds
vacuously while `p` is false, and reflexivity -- exactly what `fiveFC`/`kb5FC` drop -- is exactly
what this validity depends on. Hence `fiveValid ⊊ s5Valid` and `kb5Valid ⊊ s5Valid`
(`fiveValid_ssubset_s5Valid`, `kb5Valid_ssubset_s5Valid`, with supporting `boxImp_s5Valid`,
`boxImp_not_fiveValid`, `boxImp_not_kb5Valid`, `fiveValid_imp_s5Valid`, `kb5Valid_imp_s5Valid`,
`s5FC_imp_fiveFC`, `s5FC_imp_kb5FC` in the probe): **no sound+complete decision procedure for
`s5Valid` composes into one for `fiveValid`/`kb5Valid`**, no matter how the S5 tableau itself is
built or proven.

**This is a route obstruction, NOT an impossibility of the deliverable.** 5 (Euclidean) validity
and completeness ARE delivered -- by a dedicated Euclidean route built on top of the S5 cluster
machinery (`modalTableauFive`, consuming a new `Relation.EuclGen` least-closure operator in
`Cslib/Foundations/Relation/Euclidean.lean`): rooted Euclidean frames are exactly "root + universal
cluster" (`Relation.RightEuclidean.equiv_cod`, `Euclidean.lean:124`), so the cluster half is the S5
machinery this file's neighbours already build, and only the closure operator and a root-aware
rule are genuinely new. KB5's **rule and soundness** are delivered too (`modalApplyOneKb5`,
`modalTableauKb5_sound`, by a "factor, not clone" frame-class-monotonicity argument: the
unmodified Five rule is already sound for the strictly stronger `kb5FC` class). **KB5
completeness is the one piece that remains open** -- `modalApplyOneFive`'s root-restricted
propagation, essential to Five's own soundness, is provably insufficient once the frame is required
to be symmetric too; see the dedicated blocker note beside `extractModelKb5` below for the precise
argument and a machine-checked scout lemma. This is a **rule-design gap for the completeness
direction**, not an impossibility: K5/KB5 completeness via a rooted Euclidean tableau is standard
in the literature (Blackburn–de Rijke–Venema §4.8-4.9).

**Genuine pure-K5 / pure-5** (Euclidean *without* full equivalence -- i.e. a frame satisfying only
`RightEuclidean`, and for KB5 additionally `Std.Symm`, but not necessarily `Std.Refl`/`IsTrans` as
freestanding properties) is no longer missing library infrastructure. The bespoke `Relation.EuclGen`
closure operator (`Cslib/Foundations/Relation/Euclidean.lean`) -- the least right-Euclidean relation
containing a given relation, built exactly because Mathlib ships no such "Euclidean closure"
analogous to `Relation.EqvGen`/`Relation.SymmGen` -- lands the countermodel extractor
`extractModelFive` (5, via `EuclGen acc.hasEdge`, complete) and `extractModelKb5` (KB5, via a
symmetric variant of the same closure, extraction infrastructure landed but its truth lemma and
completeness theorem blocked, see below) together with `modalTruthLemmaFive` and the completeness
theorem `modalTableauFive_complete`. `extractModelS5` itself remains untouched and is not the route
pure-K5/5 uses. -/

/-! ## T Modal Truth Lemma (task 503 Phase 5)

`modalExpandBranchesT_hintikka` (`TDriver.lean`, delivered by task 510) produces a
`modalHintikkaSetGen modalApplyOneT bR aR` witness from an open `modalExpandBranchesT` result.
This section closes the remaining gap: the T truth lemma against `extractModelT` and `tValid`
completeness.

`modalApplyOneT` agrees with `modalApplyOne` outside the box-positive/diamond-negative shapes
(`modalApplyOneT_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), so every propositional case and
the box-negative/diamond-positive modal cases reduce to exactly the K argument (the latter two
via the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`,
`Completeness.lean`, task 510). The box-positive and diamond-negative cases are genuinely new:
`hintikkaT_box_pos`/`hintikkaT_diamond_neg` below combine the K argument (raw recorded edge,
`Relation.ReflGen.single`) with the T self-propagation conjunct (reflexive self-edge,
`Relation.ReflGen.refl`), as task 510's own research anticipated
(`hintikka_box_pos`/`hintikka_diamond_neg` are payload-reading and irreducibly K-specific). -/

omit [Hashable Atom] in
/-- `modalApplyOneT` agrees with `modalApplyOne` on every signed formula whose formula
component is neither `box`- nor `diamond`-shaped (regardless of sign) -- specialization of
`modalApplyOneT_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`) used by the propositional cases of
`modalTruthLemmaT` below (mirrors `FrameSoundness.lean`'s S4 analog
`modalApplyOneS4_eq_of_not_modal_shaped`, simplified to T's single-layer dispatch). -/
private lemma modalApplyOneT_eq_of_not_box_diamond
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    modalApplyOneT sf b acc = modalApplyOne sf b acc :=
  modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩

omit [Hashable Atom] in
/-- Local re-derivation of `TDriver.lean`'s `private lemma modalApplyOneT_boxPos_fst` (that
lemma is `private` to its own file, hence unavailable here): direct unfolding of
`modalApplyOneT`'s `.fst` component at a box-positive shaped signed formula, in terms of the
underlying `modalApplyOne` (K) result. Proof reproduced verbatim (three lines), not
re-designed. -/
private lemma modalApplyOneT_boxPos_fst'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.pos, .box φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalTBoxSelf b φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTBoxSelf b φ w).isEmpty then .notApplicable
            else .persistent (modalTBoxSelf b φ w)
          | other => other) := by
  simp only [modalApplyOneT]
  cases (modalApplyOne (⟨.pos, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- Symmetric to `modalApplyOneT_boxPos_fst'` for the diamond-negative shape. -/
private lemma modalApplyOneT_diamondNeg_fst'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneT (⟨.neg, .diamond φ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = (match (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            .persistent (kForms ++
              (modalTDiaNegSelf b φ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTDiaNegSelf b φ w).isEmpty then .notApplicable
            else .persistent (modalTDiaNegSelf b φ w)
          | other => other) := by
  simp only [modalApplyOneT]
  cases (modalApplyOne (⟨.neg, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst <;>
    first | rfl | (split_ifs <;> rfl)

omit [Hashable Atom] in
/-- `modalTBoxSelf b φ w = []` iff `T(φ)@w` is already on the branch (direct unfolding of
`modalTBoxSelf`'s `if`-guard). -/
private lemma modalTBoxSelf_eq_nil_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalTBoxSelf b φ w = [] ↔
      (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  simp only [modalTBoxSelf]
  split_ifs with h
  · simpa using h
  · simp only [false_iff]
    simpa using h

omit [Hashable Atom] in
/-- Symmetric to `modalTBoxSelf_eq_nil_iff` for `modalTDiaNegSelf`. -/
private lemma modalTDiaNegSelf_eq_nil_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    modalTDiaNegSelf b φ w = [] ↔
      (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  simp only [modalTDiaNegSelf]
  split_ifs with h
  · simpa using h
  · simp only [false_iff]
    simpa using h

omit [Hashable Atom] in
/-- If `modalTBoxSelf b φ w ≠ []`, it is exactly the singleton `[T(φ)@w]`, with `T(φ)@w ∉ b`
(the negation of `modalTBoxSelf_eq_nil_iff`, unfolded to expose the singleton payload). -/
private lemma modalTBoxSelf_cases_of_ne_nil
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {φ : Proposition Atom}
    {w : WorldIndex} (hself : modalTBoxSelf b φ w ≠ []) :
    modalTBoxSelf b φ w = [(⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)] ∧
      (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  simp only [modalTBoxSelf] at hself ⊢
  split_ifs at hself ⊢ with h
  · exact absurd rfl hself
  · exact ⟨rfl, by simpa using h⟩

omit [Hashable Atom] in
/-- Symmetric to `modalTBoxSelf_cases_of_ne_nil` for `modalTDiaNegSelf`. -/
private lemma modalTDiaNegSelf_cases_of_ne_nil
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {φ : Proposition Atom}
    {w : WorldIndex} (hself : modalTDiaNegSelf b φ w ≠ []) :
    modalTDiaNegSelf b φ w = [(⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)] ∧
      (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  simp only [modalTDiaNegSelf] at hself ⊢
  split_ifs at hself ⊢ with h
  · exact absurd rfl hself
  · exact ⟨rfl, by simpa using h⟩

/-- **T-analog of `hintikka_box_pos`** (`Completeness.lean`, genuinely new content -- not
inherited from K, per task 510's research note that this bridge is payload-reading and
irreducibly K-specific): `T(□ψ)@w ∈ b` together with the reflexive closure
`Relation.ReflGen acc.hasEdge w w'` (i.e. `w' = w` or a raw recorded edge `w → w'`) and
`modalHintikkaSetGen modalApplyOneT b acc` imply `T(ψ)@w' ∈ b`.

The `.refl` case (`w' = w`) is the genuinely-new T box-positive self-propagation conjunct: either
`modalTBoxSelf b ψ w = []` (meaning `T(ψ)@w` is already on the branch,
`modalTBoxSelf_eq_nil_iff`) or `modalApplyOneT`'s merged persistent output forces it in
(`modalApplyOneT_boxPos_fst'`). The `.single` case (raw edge) reduces to the same
`boxPropagation`-membership argument `hintikka_box_pos` inlines, since T's persistent output at
this shape is K's own `kForms` merged with the self-conjunct at a possibly-different world, so
`kForms` (hence the K successor witness) survives into T's merged forcing list unchanged. -/
lemma hintikkaT_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneT b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.ReflGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  cases hr with
  | refl =>
    rcases eq_or_ne (modalTBoxSelf b ψ w) [] with hself | hself
    · exact (modalTBoxSelf_eq_nil_iff b ψ w).mp hself
    · rw [modalApplyOneT_boxPos_fst'] at hcond
      rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
      · rw [hk] at hcond
        simp only [List.isEmpty_iff, hself, if_false] at hcond
        obtain ⟨heq, -⟩ := modalTBoxSelf_cases_of_ne_nil hself
        exact hcond (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) (by rw [heq]; simp)
      · rw [hk] at hcond
        obtain ⟨heq, hnotin⟩ := modalTBoxSelf_cases_of_ne_nil hself
        by_cases hkf : (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
        · exact hcond _ (List.mem_append_left _ hkf)
        · refine hcond (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (List.mem_append_right kForms ?_)
          rw [heq]
          simp only [List.mem_filter, List.mem_singleton, true_and]
          simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
          intro x hx heq
          exact hkf (heq ▸ hx)
  | single hedge =>
    by_contra hnotin
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hedge
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hedge
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    have hmemBP : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        boxPropagation b acc ψ w := by
      simp only [boxPropagation, List.mem_filterMap]
      refine ⟨w', hw'_succ, ?_⟩
      rw [if_neg]
      simp only [List.any_eq_true, not_exists]
      rintro x ⟨hx, heq⟩
      rw [beq_iff_eq] at heq
      exact hnotin (heq ▸ hx)
    have hne : boxPropagation b acc ψ w ≠ [] := fun h => by simp [h] at hmemBP
    have hk : (modalApplyOne (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst = .persistent (boxPropagation b acc ψ w) := by
      simp only [modalApplyOne]
      have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
          (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
          = false := by
        rw [tryAllPropRules_pos]
        simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
      rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
    rw [modalApplyOneT_boxPos_fst', hk] at hcond
    exact hnotin (hcond (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
      (List.mem_append_left _ hmemBP))

/-- **T-analog of `hintikka_diamond_neg`** (`Completeness.lean`, genuinely new content, dual of
`hintikkaT_box_pos`): `F(◇ψ)@w ∈ b` together with `Relation.ReflGen acc.hasEdge w w'` imply
`F(ψ)@w' ∈ b`. -/
lemma hintikkaT_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneT b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.ReflGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  cases hr with
  | refl =>
    rcases eq_or_ne (modalTDiaNegSelf b ψ w) [] with hself | hself
    · exact (modalTDiaNegSelf_eq_nil_iff b ψ w).mp hself
    · rw [modalApplyOneT_diamondNeg_fst'] at hcond
      rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
      · rw [hk] at hcond
        simp only [List.isEmpty_iff, hself, if_false] at hcond
        obtain ⟨heq, -⟩ := modalTDiaNegSelf_cases_of_ne_nil hself
        exact hcond (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) (by rw [heq]; simp)
      · rw [hk] at hcond
        obtain ⟨heq, hnotin⟩ := modalTDiaNegSelf_cases_of_ne_nil hself
        by_cases hkf : (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
        · exact hcond _ (List.mem_append_left _ hkf)
        · refine hcond (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (List.mem_append_right kForms ?_)
          rw [heq]
          simp only [List.mem_filter, List.mem_singleton, true_and]
          simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
          intro x hx heq
          exact hkf (heq ▸ hx)
  | single hedge =>
    by_contra hnotin
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hedge
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hedge
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    have hmemDN : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        (acc.successorsOf w).filterMap (fun w'' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
          if b.any (· == sf') then none else some sf') := by
      simp only [List.mem_filterMap]
      refine ⟨w', hw'_succ, ?_⟩
      rw [if_neg]
      simp only [List.any_eq_true, not_exists]
      rintro x ⟨hx, heq⟩
      rw [beq_iff_eq] at heq
      exact hnotin (heq ▸ hx)
    have hne : (acc.successorsOf w).filterMap (fun w'' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
        if b.any (· == sf') then none else some sf') ≠ [] :=
      fun h => by rw [h] at hmemDN; exact absurd hmemDN (List.not_mem_nil)
    have hk : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        .persistent ((acc.successorsOf w).filterMap (fun w'' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
          if b.any (· == sf') then none else some sf')) := by
      simp only [modalApplyOne]
      have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
          (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
          = false := by
        rw [tryAllPropRules_neg]
        simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
      rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
    rw [modalApplyOneT_diamondNeg_fst', hk] at hcond
    exact hnotin (hcond (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
      (List.mem_append_left _ hmemDN))

/-- **T Modal Truth Lemma**: membership in a T Hintikka branch tracks satisfaction in the
extracted reflexive Kripke model `extractModelT b acc`.

Proof by strong induction on `modalComplexity φ`, mirroring `modalTruthLemma` (`Completeness.lean`):
the propositional cases (`atom`/`bot`/`imp`/`and`/`or`) reuse the public, apply-agnostic
consistency kit and K's `modalApplyOne_*` bridge lemmas verbatim, routed through
`modalApplyOneT_eq_of_not_box_diamond`; the box-negative/diamond-positive cases reuse the free
generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` (task 510) directly
(unaffected minting shapes); the box-positive/diamond-negative cases consume the genuinely-new
`hintikkaT_box_pos`/`hintikkaT_diamond_neg` bridges above, with the model's `r w w'` unfolding to
exactly the `Relation.ReflGen` hypothesis those bridges want (`extractModelT_r`). -/
lemma modalTruthLemmaT
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneT b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelT b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelT b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelT b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelT b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelT b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelT b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelT, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelT, extractModelWith, List.any_eq_true] at hsat
        obtain ⟨sf, hsf_mem, hcond⟩ := hsat
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
        have hsign_eq : sf.sign = .pos := eq_of_beq hsign
        have hform_eq : sf.formula = .atom p := eq_of_beq hform
        have hlab_eq : sf.label = w := eq_of_beq hlab
        have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
          convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
        exact openBranch_noContradiction b hHopen (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hHopen w), ?_⟩
      intro _ hsat
      exact hsat
    | imp a c =>
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hHrule ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneT_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        have hpath : Relation.ReflGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelT_r b acc ▸ hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaT_box_pos b acc hH ψ w w' hmem hpath)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneT b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelT_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneT b acc hH ψ w hmem
        exact ⟨w', extractModelT_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.ReflGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelT_r b acc ▸ hw'
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaT_diamond_neg b acc hH ψ w w' hmem hpath) hsψ

/-- An open T Hintikka branch with `F(φ)@0 ∈ b` yields a reflexive Kripke countermodel to `φ`.
Mirrors `modalOpenBranch_countermodel` (`Completeness.lean`). -/
theorem modalOpenBranchT_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hH : modalHintikkaSetGen modalApplyOneT b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelT b acc) 0 φ :=
  (modalTruthLemmaT b acc hH φ 0).2 hF

/-! ## Task 513 Phase 5: T Soundness Discharges + `modalTableauT_sound` -/

omit [Hashable Atom] in
/-- **Task 513 (Phase 5, S-agree for T)**: `modalApplyOneT` agrees with `modalApplyOne` off
the two propagating shapes -- exactly `modalApplyOneT_eq_of_not_boxPos_diaNeg`
(`FrameRules.lean`) verbatim; zero new proof content. Discharges
`modalStepBranchGen_preserves_satIn`/`modalExpandBranchesGen_closed_unsatIn`'s `hAgree`
hypothesis at `apply := modalApplyOneT`. -/
theorem hAgreeT
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneT sf b acc = modalApplyOne sf b acc :=
  modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc h

/-- **Task 513 (Phase 5, S-boxPos for T)**: frame-relativized semantic soundness of
`modalApplyOneT`'s box-positive output at `FC := reflFC`. Splits `RuleResultSat` over the
`kForms ++ selfNew.filter …` append (`modalApplyOneT_boxPos_fst`, `TDriver.lean`): the
`kForms` half is Phase 1's `modalApplyOne_boxPos_sound` (K, `FC` unused); the `selfNew` half
(at most one extra formula, `T(φ)@lbl` from `T(□φ)@lbl` at the *same* world) is justified
directly by reflexivity (`hFC.refl (f lbl) : m.r (f lbl) (f lbl)`), mirroring
`branchSatisfiableIn_reflFC_boxPos_mem`/`modalTBoxSelf_sound`
(`FrameSoundness.lean`) inline (those lemmas existentially quantify their own witnessing model,
so cannot be applied as black boxes to the caller's specific `(m, f)`; the reflexivity
insight is the same). -/
theorem modalApplyOneT_boxPos_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : reflFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneT
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneT
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqK, hRRSK⟩ := modalApplyOne_boxPos_sound m f φ lbl b acc hacc hb hmem
  have hselfSat : Satisfies m (f lbl) φ := by
    have hbox : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
    simp only [Satisfies] at hbox
    exact hbox (f lbl) (hFC.refl (f lbl))
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneT_boxPos_snd]; exact hsndeqK
  · rw [modalApplyOneT_boxPos_fst]
    rcases modalApplyOne_boxPos_eq
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc with
        hk | ⟨kForms, hk⟩
    · rw [hk] at hRRSK ⊢
      split_ifs with hemp
      · trivial
      · intro sf' hmem'
        simp only [modalTBoxSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_pos m f φ lbl hselfSat
    · rw [hk] at hRRSK ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSK sf' hmem'
      · simp only [modalTBoxSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_pos m f φ lbl hselfSat

/-- **Task 513 (Phase 5, S-diaNeg for T)**: dual of `modalApplyOneT_boxPos_soundIn` for the
diamond-negative shape. -/
theorem modalApplyOneT_diaNeg_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : reflFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem :
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneT
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneT
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqK, hRRSK⟩ := modalApplyOne_diaNeg_sound m f φ lbl b acc hacc hb hmem
  have hselfSat : ¬ Satisfies m (f lbl) φ := by
    have hdia : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
    rw [Satisfies.diamond_iff] at hdia
    push Not at hdia
    exact hdia (f lbl) (hFC.refl (f lbl))
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneT_diamondNeg_snd]; exact hsndeqK
  · rw [modalApplyOneT_diamondNeg_fst]
    rcases modalApplyOne_diamondNeg_eq
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        with hk | ⟨kForms, hk⟩
    · rw [hk] at hRRSK ⊢
      split_ifs with hemp
      · trivial
      · intro sf' hmem'
        simp only [modalTDiaNegSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_neg m f φ lbl hselfSat
    · rw [hk] at hRRSK ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSK sf' hmem'
      · simp only [modalTDiaNegSelf] at hmem'
        split_ifs at hmem' with hcase
        · simp at hmem'
        · simp only [List.mem_singleton] at hmem'
          subst hmem'
          exact sfSat_neg m f φ lbl hselfSat

/-- **Task 513 (Phase 5)**: `modalTableauT` is sound: if the T tableau closes on `F(φ)`, then
`φ` is `tValid`. Contrapositive over `reflFC`, mirroring `modalTableau_sound`
(`Soundness.lean`) and the K zero-regression derivation `modalTableau_sound_frame_gen`
(`FrameSoundness.lean`, Phase 4): feeds `modalExpandBranchesGen_closed_unsatIn reflFC
modalApplyOneT` at the initial configuration `[[F(φ)@0]] [[]] [Accessibility.empty]`. The
initial `branchSatisfiableIn reflFC` witness uses the reflexive falsifying model directly
(available since `tValid = frameValid reflFC` quantifies only reflexive models, so the
`by_contra` model is reflexive by hypothesis). -/
theorem modalTableauT_sound (φ : Proposition Atom) (h : modalTableauT φ = .closed) :
    tValid φ := by
  intro World m hrefl w
  by_contra hnotsat
  have hsat : branchSatisfiableIn reflFC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, hrefl,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hunsat := modalExpandBranchesGen_closed_unsatIn reflFC modalApplyOneT
    modalApplyOneT_spec.freshLocal
    hAgreeT
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneT_boxPos_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneT_diaNeg_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons (accFreshInv_empty _) List.Forall₂.nil)
    (by
      have h' : modalExpandBranchesT
          [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
          [Accessibility.empty] (modalFuel φ) = .closed := h
      exact h')
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

/-! ## `tValid` Completeness -/

/-- **T-completeness of the modal tableau** (task 503 Phase 5): if the T tableau on `φ0` returns
an open branch, `φ0` is not T-valid. Mirrors `modalTableau_complete`
(`CompletenessLoop.lean`): combines `modalExpandBranchesT_hintikka` (task 510, `TDriver.lean`)
instantiated at the initial configuration (via `modalLoopInvGen_initial` and the fuel bridge
`modalExpMeasure_entry_le_fuel`, both un-privatized for this purpose per their own docstrings),
the generic initial-branch membership persistence lemma
(`modalExpandBranchesGen_openBranch_initial_mem`, likewise), and the T countermodel extraction
above. -/
theorem modalTableauT_complete (φ0 : Proposition Atom)
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {a : Accessibility}
    (h : modalTableauT φ0 = .openBranch b a) :
    ¬ tValid φ0 := by
  have h' : modalExpandBranchesT
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      [Accessibility.empty] (modalFuel φ0) = .openBranch b a := h
  have hmeas := modalExpMeasure_entry_le_fuel φ0
  have hInv : ∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
      (ai : Accessibility),
      ([[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]])[i]? = some bi →
      (([[]] : List (List (SignedFormula (Proposition Atom) WorldIndex))))[i]? = some ei →
      ([Accessibility.empty])[i]? = some ai →
      ∃ rank, ModalLoopInvGen modalApplyOneT φ0 bi ei ai rank := by
    intro i bi ei ai hib hie hia
    match i with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
      subst hib; subst hie; subst hia
      exact ⟨fun _ => modalDepth φ0, modalLoopInvGen_initial modalApplyOneT φ0⟩
    | n + 1 => simp at hib
  have hH : modalHintikkaSetGen modalApplyOneT b a :=
    modalExpandBranchesT_hintikka φ0 (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl hmeas hInv b a h'
  have hmemInit : (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    modalExpandBranchesGen_openBranch_initial_mem modalApplyOneT (modalFuel φ0)
      (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (fun b₀ hb₀ => by
        simp only [List.mem_singleton] at hb₀
        subst hb₀
        simp)
      b a h'
  have hnot := modalOpenBranchT_countermodel b a φ0 hH hmemInit
  intro htv
  exact hnot (htv WorldIndex (extractModelT b a) (extractModelT_refl b a) 0)

/-! ## Task 513 Phase 6: `tValid` Decidability -/

/-- **The modal T tableau decides T-validity** (task 513 Phase 6 / task 503 Phase 6 target):
`modalTableauT φ0` closes exactly when `φ0` is T-valid. Combines soundness
(`modalTableauT_sound`, Phase 5) with completeness (`modalTableauT_complete`, above) via the
two-constructor dichotomy of `ModalTableauResult`. Mirrors `modalTableau_decides`
(`CompletenessLoop.lean`) line-for-line. -/
theorem tValid_decides (φ0 : Proposition Atom) :
    modalTableauT φ0 = .closed ↔ tValid φ0 := by
  constructor
  · exact modalTableauT_sound φ0
  · intro htv
    cases htab : modalTableauT φ0 with
    | closed => rfl
    | openBranch b a => exact absurd htv (modalTableauT_complete φ0 htab)

/-- **T-validity is decidable** (task 513 Phase 6 / task 503 Phase 6 target): decide by running
the modal T tableau and consulting `tValid_decides`. No `Fintype Atom` assumption is needed,
since the tableau computation itself is the decision procedure. Mirrors `instDecidableKValid`
(`CompletenessLoop.lean`) line-for-line. -/
instance instDecidableTValid (φ0 : Proposition Atom) : Decidable (tValid φ0) :=
  match h : modalTableauT φ0 with
  | .closed => .isTrue ((tValid_decides φ0).mp h)
  | .openBranch _ _ => .isFalse (modalTableauT_complete φ0 h)

/-! ## B Modal Truth Lemma (task 505 Phase 6)

`modalExpandBranchesB_hintikka` (`BDriver.lean`) produces a `modalHintikkaSetGen modalApplyOneB
bR aR` witness from an open `modalExpandBranchesB` result. This section closes the remaining
gap: the B truth lemma against `extractModelB` and `bValid` completeness.

`modalApplyOneB` agrees with `modalApplyOne` outside the box-positive/diamond-negative shapes
(`modalApplyOneB_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), so every propositional case and
the box-negative/diamond-positive modal cases reduce to exactly the K argument (the latter two
via the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`,
`Completeness.lean`, task 510) -- these only need a *forward* raw edge witness, which survives
into the symmetric closure via `extractModelB_hasEdge_imp_r` (`Or.inl`), so no B-specific content
is needed there. The box-positive and diamond-negative cases are genuinely new:
`hintikkaB_box_pos`/`hintikkaB_diamond_neg` below case-split `Relation.SymmGen`'s two disjuncts --
the *forward* disjunct reduces to the same `boxPropagation`-membership argument
`hintikka_box_pos`/`hintikkaT_box_pos` inline (K's own successor forcing, unaffected by B's
merged output since `modalApplyOneB`'s persistent output is K's own `kForms` merged with the
backward conjunct); the *backward* disjunct is B's own genuinely new content, forcing via
`modalBBoxBack`/`modalBDiaNegBack`'s known-worlds-filtered predecessor propagation
(`FrameRules.lean`), with the known-worlds side condition discharged by `accSourcesKnown`
(`BDriver.lean`) -- the source-side twin of `accTargetsKnown` this development introduces
precisely because B propagates to edge *sources*. -/

omit [Hashable Atom] in
/-- `modalApplyOneB` agrees with `modalApplyOne` on every signed formula whose formula
component is neither `box`- nor `diamond`-shaped (regardless of sign) -- specialization of
`modalApplyOneB_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`) used by the propositional cases of
`modalTruthLemmaB` below. -/
private lemma modalApplyOneB_eq_of_not_box_diamond
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hnb : ∀ φ, sf.formula ≠ .box φ) (hnd : ∀ φ, sf.formula ≠ .diamond φ) :
    modalApplyOneB sf b acc = modalApplyOne sf b acc :=
  modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc
    ⟨fun ⟨_, φ, h⟩ => hnb φ h, fun ⟨_, φ, h⟩ => hnd φ h⟩

/-- **B-analog of `hintikka_box_pos`/`hintikkaT_box_pos`** (genuinely new content per task 510's
research note that this bridge is payload-reading and irreducibly per-system): `T(□ψ)@w ∈ b`
together with the symmetric closure `Relation.SymmGen acc.hasEdge w w'` and `accSourcesKnown b
acc` imply `T(ψ)@w' ∈ b`.

The forward disjunct (`acc.hasEdge w w'`) reduces to the same `boxPropagation`-membership
argument `hintikkaT_box_pos`'s `.single` case inlines, since B's persistent output at this shape
is K's own `kForms` merged with the backward conjunct at possibly-different worlds, so `kForms`
(hence the K successor witness) survives into B's merged forcing list unchanged. The backward
disjunct (`acc.hasEdge w' w`, i.e. `w'` is a recorded *predecessor* of `w`) is B's own content:
`w'` is known (`accSourcesKnown`), so `modalBBoxBack_mem_of` witnesses `T(ψ)@w' ∈ modalBBoxBack
b acc ψ w`, which the saturation forcing property (`hH.2.1`) then places on `b`. -/
lemma hintikkaB_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneB b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.SymmGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  rcases hr with hfwd | hbwd
  · by_contra hnotin
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hfwd
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hfwd
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    have hmemBP : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        boxPropagation b acc ψ w := by
      simp only [boxPropagation, List.mem_filterMap]
      refine ⟨w', hw'_succ, ?_⟩
      rw [if_neg]
      simp only [List.any_eq_true, not_exists]
      rintro x ⟨hx, heq⟩
      rw [beq_iff_eq] at heq
      exact hnotin (heq ▸ hx)
    have hne : boxPropagation b acc ψ w ≠ [] := fun h => by simp [h] at hmemBP
    have hk : (modalApplyOne (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst = .persistent (boxPropagation b acc ψ w) := by
      simp only [modalApplyOne]
      have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
          (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
          = false := by
        rw [tryAllPropRules_pos]
        simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
      rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
    rw [modalApplyOneB_boxPos_fst, hk] at hcond
    exact hnotin (hcond (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
      (List.mem_append_left _ hmemBP))
  · by_contra hnotin
    have hpred : w' ∈ modalBPredecessorsOf acc w := modalBPredecessorsOf_mem_of_hasEdge hbwd
    have hknown : w' ∈ modalKnownWorlds b := hSrc w' w hbwd
    have hmemBack : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        modalBBoxBack b acc ψ w := modalBBoxBack_mem_of hpred hknown hnotin
    rw [modalApplyOneB_boxPos_fst] at hcond
    rcases modalApplyOne_boxPos_eq (⟨.pos, .box ψ, w⟩) rfl ψ rfl b acc with hk | ⟨kForms, hk⟩
    · rw [hk] at hcond
      have hne : ¬ (modalBBoxBack b acc ψ w).isEmpty := by
        simp only [List.isEmpty_iff]
        intro hcontra
        rw [hcontra] at hmemBack
        exact List.not_mem_nil hmemBack
      simp only [hne] at hcond
      exact hnotin (hcond _ hmemBack)
    · rw [hk] at hcond
      by_cases hkf : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
      · exact hnotin (hcond _ (List.mem_append_left _ hkf))
      · apply hnotin
        apply hcond
        apply List.mem_append_right
        rw [List.mem_filter]
        refine ⟨hmemBack, ?_⟩
        simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
        intro x hx heqx
        exact hkf (heqx ▸ hx)

/-- **B-analog of `hintikka_diamond_neg`/`hintikkaT_diamond_neg`**, dual of `hintikkaB_box_pos`:
`F(◇ψ)@w ∈ b` together with `Relation.SymmGen acc.hasEdge w w'` and `accSourcesKnown b acc`
imply `F(ψ)@w' ∈ b`. -/
lemma hintikkaB_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneB b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : Relation.SymmGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  rcases hr with hfwd | hbwd
  · by_contra hnotin
    have hw'_succ : w' ∈ acc.successorsOf w := by
      simp only [Accessibility.successorsOf, List.mem_filterMap]
      simp only [Accessibility.hasEdge, List.any_eq_true] at hfwd
      obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hfwd
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
    have hmemDN : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        (acc.successorsOf w).filterMap (fun w'' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
          if b.any (· == sf') then none else some sf') := by
      simp only [List.mem_filterMap]
      refine ⟨w', hw'_succ, ?_⟩
      rw [if_neg]
      simp only [List.any_eq_true, not_exists]
      rintro x ⟨hx, heq⟩
      rw [beq_iff_eq] at heq
      exact hnotin (heq ▸ hx)
    have hne : (acc.successorsOf w).filterMap (fun w'' =>
        let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
        if b.any (· == sf') then none else some sf') ≠ [] :=
      fun h => by rw [h] at hmemDN; exact absurd hmemDN (List.not_mem_nil)
    have hk : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        .persistent ((acc.successorsOf w).filterMap (fun w'' =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w''⟩
          if b.any (· == sf') then none else some sf')) := by
      simp only [modalApplyOne]
      have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
          (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
          = false := by
        rw [tryAllPropRules_neg]
        simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
      rw [if_neg (by simp [htry]), if_neg (by simpa using hne)]
    rw [modalApplyOneB_diamondNeg_fst, hk] at hcond
    exact hnotin (hcond (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)
      (List.mem_append_left _ hmemDN))
  · by_contra hnotin
    have hpred : w' ∈ modalBPredecessorsOf acc w := modalBPredecessorsOf_mem_of_hasEdge hbwd
    have hknown : w' ∈ modalKnownWorlds b := hSrc w' w hbwd
    have hmemBack : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
        modalBDiaNegBack b acc ψ w := modalBDiaNegBack_mem_of hpred hknown hnotin
    rw [modalApplyOneB_diamondNeg_fst] at hcond
    rcases modalApplyOne_diamondNeg_eq (⟨.neg, .diamond ψ, w⟩) rfl ψ rfl b acc with
        hk | ⟨kForms, hk⟩
    · rw [hk] at hcond
      have hne : ¬ (modalBDiaNegBack b acc ψ w).isEmpty := by
        simp only [List.isEmpty_iff]
        intro hcontra
        rw [hcontra] at hmemBack
        exact List.not_mem_nil hmemBack
      simp only [hne] at hcond
      exact hnotin (hcond _ hmemBack)
    · rw [hk] at hcond
      by_cases hkf : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ kForms
      · exact hnotin (hcond _ (List.mem_append_left _ hkf))
      · apply hnotin
        apply hcond
        apply List.mem_append_right
        rw [List.mem_filter]
        refine ⟨hmemBack, ?_⟩
        simp only [List.any_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
        intro x hx heqx
        exact hkf (heqx ▸ hx)

/-- **B Modal Truth Lemma**: membership in a B Hintikka branch tracks satisfaction in the
extracted symmetric Kripke model `extractModelB b acc`, given `accSourcesKnown b acc`.

Proof by strong induction on `modalComplexity φ`, mirroring `modalTruthLemmaT`: the
propositional cases reuse the public, apply-agnostic consistency kit and K's `modalApplyOne_*`
bridge lemmas verbatim, routed through `modalApplyOneB_eq_of_not_box_diamond`; the
box-negative/diamond-positive cases reuse the free generic projection bridges
`hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` directly; the box-positive/diamond-negative
cases consume the genuinely-new `hintikkaB_box_pos`/`hintikkaB_diamond_neg` bridges above, with
the model's `r w w'` unfolding to exactly the `Relation.SymmGen` hypothesis those bridges
want (`extractModelB_r`). -/
lemma modalTruthLemmaB
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneB b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelB b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelB b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelB b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelB b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelB b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelB b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelB, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelB, extractModelWith, List.any_eq_true] at hsat
        obtain ⟨sf, hsf_mem, hcond⟩ := hsat
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
        have hsign_eq : sf.sign = .pos := eq_of_beq hsign
        have hform_eq : sf.formula = .atom p := eq_of_beq hform
        have hlab_eq : sf.label = w := eq_of_beq hlab
        have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
          convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
        exact openBranch_noContradiction b hHopen (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hHopen w), ?_⟩
      intro _ hsat
      exact hsat
    | imp a c =>
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hHrule ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneB_eq_of_not_box_diamond _ b acc (by simp) (by simp)] at hcond
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        have hpath : Relation.SymmGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelB_r b acc ▸ hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaB_box_pos b acc hSrc hH ψ w w' hmem hpath)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneB b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelB_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneB b acc hH ψ w hmem
        exact ⟨w', extractModelB_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.SymmGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelB_r b acc ▸ hw'
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaB_diamond_neg b acc hSrc hH ψ w w' hmem hpath) hsψ

/-- An open B Hintikka branch with `F(φ)@0 ∈ b` (and `accSourcesKnown b acc`) yields a
symmetric Kripke countermodel to `φ`. Mirrors `modalOpenBranchT_countermodel`. -/
theorem modalOpenBranchB_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (hSrc : accSourcesKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneB b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelB b acc) 0 φ :=
  (modalTruthLemmaB b acc hSrc hH φ 0).2 hF

/-! ## `bValid` Completeness (task 505 Phase 8) -/

/-- **B-completeness of the modal tableau**: if the B tableau on `φ0` returns an open branch,
`φ0` is not B-valid. Mirrors `modalTableauT_complete`: combines `modalExpandBranchesB_hintikka`
instantiated at the initial configuration, the generic initial-branch membership persistence
lemma (`modalExpandBranchesGen_openBranch_initial_mem`), the `accSourcesKnown` top-loop
propagation lemma (`modalExpandBranchesGen_openBranch_accSourcesKnown`, `BDriver.lean`,
task 505 -- the piece with no T analogue, since T never needs known-worlds reasoning), and the
B countermodel extraction above. This direction is fully generic and does **not** depend on
task 513's soundness-chain generalization. -/
theorem modalTableauB_complete (φ0 : Proposition Atom)
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {a : Accessibility}
    (h : modalTableauB φ0 = .openBranch b a) :
    ¬ bValid φ0 := by
  have h' : modalExpandBranchesB
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      [Accessibility.empty] (modalFuel φ0) = .openBranch b a := h
  have hmeas := modalExpMeasure_entry_le_fuel φ0
  have hInv : ∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
      (ai : Accessibility),
      ([[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]])[i]? = some bi →
      (([[]] : List (List (SignedFormula (Proposition Atom) WorldIndex))))[i]? = some ei →
      ([Accessibility.empty])[i]? = some ai →
      ∃ rank, ModalLoopInvGen modalApplyOneB φ0 bi ei ai rank := by
    intro i bi ei ai hib hie hia
    match i with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
      subst hib; subst hie; subst hia
      exact ⟨fun _ => modalDepth φ0, modalLoopInvGen_initial modalApplyOneB φ0⟩
    | n + 1 => simp at hib
  have hH : modalHintikkaSetGen modalApplyOneB b a :=
    modalExpandBranchesB_hintikka φ0 (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl hmeas hInv b a h'
  have hSrc : accSourcesKnown b a :=
    modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneB modalApplyOneB_spec.freshLocal
      (modalFuel φ0)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (by
        intro p hp
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
        subst hp
        exact accSourcesKnown_empty _)
      b a h'
  have hmemInit : (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    modalExpandBranchesGen_openBranch_initial_mem modalApplyOneB (modalFuel φ0)
      (⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
      [[(⟨.neg, φ0, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]] [Accessibility.empty]
      rfl rfl
      (fun b₀ hb₀ => by
        simp only [List.mem_singleton] at hb₀
        subst hb₀
        simp)
      b a h'
  have hnot := modalOpenBranchB_countermodel b a φ0 hSrc hH hmemInit
  intro htv
  exact hnot (htv WorldIndex (extractModelB b a) (extractModelB_symm b a) 0)

/-! ## Task 505 Phase 9: B Soundness Discharges + `modalTableauB_sound`

Task 513 landed (during this dispatch) the generalized frame-relativized soundness chain
(`modalStepBranchGen_preserves_satIn`/`modalExpandBranchesGen_closed_unsatIn`,
`FrameSoundness.lean`), taking three raw hypotheses (`hAgree`/`hBoxPos`/`hDiaNeg`) rather than
a hard-coded `modalApplyOne`. B's soundness side therefore only needs to supply its own
`hAgree`/`hBoxPos`/`hDiaNeg` triple and instantiate -- mirroring exactly how task 513 itself
instantiated T (`hAgreeT`, `modalApplyOneT_boxPos_soundIn`, `modalApplyOneT_diaNeg_soundIn`,
`modalTableauT_sound`). This closes the loop the plan originally isolated as a `[BLOCKED]`
Phase 9 fallback: no fallback is needed since task 513 landed before this phase ran. -/

omit [Hashable Atom] in
/-- **S-agree for B**: `modalApplyOneB` agrees with `modalApplyOne` off the two propagating
shapes -- exactly `modalApplyOneB_eq_of_not_boxPos_diaNeg` (`FrameRules.lean`) verbatim; zero
new proof content. Discharges `modalStepBranchGen_preserves_satIn`/
`modalExpandBranchesGen_closed_unsatIn`'s `hAgree` hypothesis at `apply := modalApplyOneB`. -/
theorem hAgreeB
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneB sf b acc = modalApplyOne sf b acc :=
  modalApplyOneB_eq_of_not_boxPos_diaNeg sf b acc h

/-- **S-boxPos for B**: frame-relativized semantic soundness of `modalApplyOneB`'s box-positive
output at `FC := symmFC`. Splits `RuleResultSat` over the `kForms ++ backNew.filter …` append
(`modalApplyOneB_boxPos_fst`, `BDriver.lean`): the `kForms` half is K's own
`modalApplyOne_boxPos_sound` (`FC` unused); the `backNew` half (backward-propagated formulas at
recorded predecessors) is justified by symmetry -- each `x ∈ modalBBoxBack b acc φ lbl` has
`x.label` a predecessor `v` (edge `v → lbl`), so `hacc` gives `m.r (f v) (f lbl)`, symmetry
(`hFC.symm`) gives `m.r (f lbl) (f v)`, and `T(□φ)@lbl`'s box unfolding then places `φ` at
`f v`. -/
theorem modalApplyOneB_boxPos_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : symmFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem : (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneB
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd = acc ∧
    RuleResultSat m f (modalApplyOneB
      (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqK, hRRSK⟩ := modalApplyOne_boxPos_sound m f φ lbl b acc hacc hb hmem
  have hbox : Satisfies m (f lbl) (.box φ) := (hb _ hmem).1 rfl
  have hback : ∀ sf' ∈ modalBBoxBack b acc φ lbl, sfSat m f sf' := by
    intro sf' hmem'
    obtain ⟨hxeq, hpred, -, -⟩ := modalBBoxBack_mem hmem'
    have hedge : acc.hasEdge sf'.label lbl = true := modalBPredecessorsOf_hasEdge hpred
    have hmvw : m.r (f sf'.label) (f lbl) := hacc _ _ hedge
    have hmwv : m.r (f lbl) (f sf'.label) := hFC.symm (f sf'.label) (f lbl) hmvw
    rw [hxeq]
    exact sfSat_pos m f φ sf'.label (hbox (f sf'.label) hmwv)
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneB_boxPos_snd]; exact hsndeqK
  · rw [modalApplyOneB_boxPos_fst]
    rcases modalApplyOne_boxPos_eq
        (⟨.pos, .box φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc with
        hk | ⟨kForms, hk⟩
    · rw [hk] at hRRSK ⊢
      split_ifs with hemp
      · trivial
      · exact hback
    · rw [hk] at hRRSK ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSK sf' hmem'
      · exact hback sf' hmem'

/-- **S-diaNeg for B**: dual of `modalApplyOneB_boxPos_soundIn` for the diamond-negative
shape. -/
theorem modalApplyOneB_diaNeg_soundIn
    {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hFC : symmFC m.r)
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hmem :
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (modalApplyOneB
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
        = acc ∧
    RuleResultSat m f (modalApplyOneB
      (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst := by
  obtain ⟨hsndeqK, hRRSK⟩ := modalApplyOne_diaNeg_sound m f φ lbl b acc hacc hb hmem
  have hdia : ¬ Satisfies m (f lbl) (.diamond φ) := (hb _ hmem).2 rfl
  have hback : ∀ sf' ∈ modalBDiaNegBack b acc φ lbl, sfSat m f sf' := by
    intro sf' hmem'
    obtain ⟨hxeq, hpred, -, -⟩ := modalBDiaNegBack_mem hmem'
    have hedge : acc.hasEdge sf'.label lbl = true := modalBPredecessorsOf_hasEdge hpred
    have hmvw : m.r (f sf'.label) (f lbl) := hacc _ _ hedge
    have hmwv : m.r (f lbl) (f sf'.label) := hFC.symm (f sf'.label) (f lbl) hmvw
    have hnotsat : ¬ Satisfies m (f sf'.label) φ := fun hφ =>
      hdia (Satisfies.diamond_iff.mpr ⟨f sf'.label, hmwv, hφ⟩)
    rw [hxeq]
    exact sfSat_neg m f φ sf'.label hnotsat
  refine ⟨?_, ?_⟩
  · rw [modalApplyOneB_diamondNeg_snd]; exact hsndeqK
  · rw [modalApplyOneB_diamondNeg_fst]
    rcases modalApplyOne_diamondNeg_eq
        (⟨.neg, .diamond φ, lbl⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        with hk | ⟨kForms, hk⟩
    · rw [hk] at hRRSK ⊢
      split_ifs with hemp
      · trivial
      · exact hback
    · rw [hk] at hRRSK ⊢
      intro sf' hmem'
      simp only [List.mem_append, List.mem_filter] at hmem'
      rcases hmem' with hmem' | ⟨hmem', -⟩
      · exact hRRSK sf' hmem'
      · exact hback sf' hmem'

/-- **`modalTableauB` is sound**: if the B tableau closes on `F(φ)`, then `φ` is `bValid`.
Contrapositive over `symmFC`, mirroring `modalTableauT_sound`: feeds
`modalExpandBranchesGen_closed_unsatIn symmFC modalApplyOneB` at the initial configuration
`[[F(φ)@0]] [[]] [Accessibility.empty]`. The initial `branchSatisfiableIn symmFC` witness uses
the symmetric falsifying model directly (available since `bValid = frameValid symmFC`
quantifies only symmetric models, so the `by_contra` model is symmetric by hypothesis). -/
theorem modalTableauB_sound (φ : Proposition Atom) (h : modalTableauB φ = .closed) :
    bValid φ := by
  intro World m hsymm w
  by_contra hnotsat
  have hsat : branchSatisfiableIn symmFC [⟨.neg, φ, 0⟩] Accessibility.empty :=
    ⟨World, m, fun _ => w, hsymm,
      fun w1 w2 hedge => absurd hedge (by simp [Accessibility.empty, Accessibility.hasEdge]),
      fun sf hmem => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst hmem
        exact ⟨fun h => by simp at h, fun _ => hnotsat⟩⟩
  have hunsat := modalExpandBranchesGen_closed_unsatIn symmFC modalApplyOneB
    modalApplyOneB_spec.freshLocal
    hAgreeB
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneB_boxPos_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (fun m f φ lbl b acc hFC hacc hb hmem =>
      modalApplyOneB_diaNeg_soundIn m f φ lbl b acc hFC hacc hb hmem)
    (modalFuel φ)
    [[⟨.neg, φ, 0⟩]] [[]] [Accessibility.empty]
    rfl rfl
    (List.Forall₂.cons (accFreshInv_empty _) List.Forall₂.nil)
    (by
      have h' : modalExpandBranchesB
          [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
          [Accessibility.empty] (modalFuel φ) = .closed := h
      exact h')
  cases hunsat with
  | cons h_unsat _ => exact h_unsat hsat

/-! ## `bValid` Decidability -/

/-- **The modal B tableau decides B-validity**: `modalTableauB φ0` closes exactly when `φ0` is
B-valid. Combines soundness (`modalTableauB_sound`) with completeness
(`modalTableauB_complete`, Phase 8) via the two-constructor dichotomy of
`ModalTableauResult`. Mirrors `tValid_decides` line-for-line. -/
theorem bValid_decides (φ0 : Proposition Atom) :
    modalTableauB φ0 = .closed ↔ bValid φ0 := by
  constructor
  · exact modalTableauB_sound φ0
  · intro htv
    cases htab : modalTableauB φ0 with
    | closed => rfl
    | openBranch b a => exact absurd htv (modalTableauB_complete φ0 htab)

/-- **B-validity is decidable**: decide by running the modal B tableau and consulting
`bValid_decides`. No `Fintype Atom` assumption is needed, since the tableau computation itself
is the decision procedure. Mirrors `instDecidableTValid` line-for-line. -/
instance instDecidableBValid (φ0 : Proposition Atom) : Decidable (bValid φ0) :=
  match h : modalTableauB φ0 with
  | .closed => .isTrue ((bValid_decides φ0).mp h)
  | .openBranch _ _ => .isFalse (modalTableauB_complete φ0 h)

/-! ## S5 Modal Truth Lemma (task 515 Phase 8 / task 504 Phase 4)

`extractModelS5`'s relation is the *equivalence closure* `Relation.EqvGen acc.hasEdge`
(`extractModelS5_r`) -- worlds an arbitrary alternating chain of recorded edges apart are
related, far more than the single raw edge K's box-positive bridge consumes, and more even than
B's `Relation.SymmGen`. The S5 universal rule is exactly what pays for this: `modalApplyOneS5`'s
`T(□φ)@w` arm emits `modalS5BoxAll b φ w`, i.e. `T(φ)@w'` for **every** known world `w'` of the
branch, so a saturated branch already carries a box's payload at every known world. No path
reasoning is needed at all -- the S5 bridges below take a bare `w' ∈ modalKnownWorlds b` where
T's/B's take a `ReflGen`/`SymmGen` path. This is the sense in which S5's universal rule
"trivialises" the truth lemma, and it is why the truth lemma is reachable even though the S5
*termination* chain needs the whole keys-aware pigeonhole apparatus.

The only remaining obligation is that `Relation.EqvGen acc.hasEdge` never leaves the known-world
set, supplied by `eqvGen_mem_modalKnownWorlds_iff` below.

This section is **independent of the S5 termination chain** (`S5LoopInv`, Phases 3-6) and of the
still-unbuilt spec-free Hintikka lift: like `modalTruthLemmaT`/`modalTruthLemmaB`, it consumes a
`modalHintikkaSetGen modalApplyOneS5 b acc` witness as a *hypothesis*. It is therefore the half
of S5 completeness that does not route through `RuleApplicationSpec` -- see this file's "5 / KB5
Coverage" note and `S5Simplification.lean`'s `modalApplyOneS5_rankStep_not_dischargeable`. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- The equivalence closure of `acc.hasEdge` never leaves `b`'s known-world set, in **both**
directions.

Stated as an `Iff` rather than the one-directional implication the box-positive case literally
consumes, because `Relation.EqvGen`'s `symm` constructor is otherwise not dischargeable by
induction: at `symm` the induction hypothesis supplies `x known → y known` while the goal needs
`y known → x known`, so the two directions must be carried together. The `rel` case is where
both `accSourcesKnown` and `accTargetsKnown` are spent, one per endpoint of a raw edge -- B's
truth lemma already needs `accSourcesKnown` for exactly this reason on the narrower
`Relation.SymmGen` (`modalOpenBranchB_countermodel`'s `hSrc` parameter). -/
lemma eqvGen_mem_modalKnownWorlds_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    {w w' : WorldIndex}
    (h : Relation.EqvGen (fun a c => acc.hasEdge a c = true) w w') :
    w ∈ modalKnownWorlds b ↔ w' ∈ modalKnownWorlds b := by
  induction h with
  | rel x y hxy => exact iff_of_true (hSrc x y hxy) (hTgt x y hxy)
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **S5-analogue of `hintikkaT_box_pos`/`hintikkaB_box_pos`** (genuinely new content): on an
`modalApplyOneS5`-saturated branch, `T(□ψ)@w ∈ b` forces `T(ψ)@v ∈ b` at **every** known world
`v` -- no accessibility path from `w` to `v` is required, which is precisely the S5 universal
rule's contribution.

The proof is a `by_contra`: if `T(ψ)@v ∉ b` then `modalS5BoxAll_mem_of` places `T(ψ)@v` in
`modalS5BoxAll b ψ w` (the dedup filter only removes formulas already on `b`), and the Hintikka
set's conjunct 2 at `T(□ψ)@w` then forces it onto `b`. The `.linear`/`.branching` arms of
`modalApplyOneS5`'s `T(□φ)` dispatch are ruled out by `modalApplyOne_boxPos_eq`, whose
existentially-quantified persistent payload exists for exactly this purpose. -/
lemma hintikkaS5_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneS5 b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hv : v ∈ modalKnownWorlds b) :
    (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalS5BoxAll b ψ w := modalS5BoxAll_mem_of hv hnotin
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  have hK := modalApplyOne_boxPos_eq
    (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  unfold modalApplyOneS5 at hcond
  rcases hp : modalApplyOne
      (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond hK
  simp only at hcond hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond
    split_ifs at hcond with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond _ hall)
  · dsimp only at hcond
    by_cases hkf : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **S5-analogue of `hintikkaT_diamond_neg`**, dual of `hintikkaS5_box_pos`: `F(◇ψ)@w ∈ b`
forces `F(ψ)@v ∈ b` at every known world `v`, via `modalS5DiaNegAll`. -/
lemma hintikkaS5_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneS5 b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hv : v ∈ modalKnownWorlds b) :
    (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalS5DiaNegAll b ψ w := modalS5DiaNegAll_mem_of hv hnotin
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  have hK := modalApplyOne_diamondNeg_eq
    (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  unfold modalApplyOneS5 at hcond
  rcases hp : modalApplyOne
      (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond hK
  simp only at hcond hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond
    split_ifs at hcond with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond _ hall)
  · dsimp only at hcond
    by_cases hkf : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **The S5 modal truth lemma** (task 515 Phase 8 / task 504 Phase 4): on an
`modalApplyOneS5`-saturated open branch whose recorded edges stay inside the known-world set,
branch membership and `extractModelS5`-satisfaction agree, at every world and both signs.

Mirrors `modalTruthLemmaT`/`modalTruthLemmaB` structurally: the propositional cases
(`atom`/`bot`/`imp`/`and`/`or`) reuse the apply-agnostic consistency kit and K's
`modalApplyOne_*` bridge lemmas verbatim, routed through
`modalApplyOneS5_eq_of_not_boxPos_diaNeg`; the box-negative/diamond-positive (minting) cases
reuse the free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`
(task 510) directly, since a raw recorded edge survives into the equivalence closure via
`extractModelS5_hasEdge_imp_r`.

The box-positive/diamond-negative cases are where S5 differs from every other system in the
file: rather than following a path, they observe that `extractModelS5`'s `EqvGen` relation
cannot escape `modalKnownWorlds b` (`eqvGen_mem_modalKnownWorlds_iff`), and then read off the
payload from the universal-rule bridges `hintikkaS5_box_pos`/`hintikkaS5_diamond_neg`. -/
lemma modalTruthLemmaS5
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneS5 b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS5 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS5 b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelS5 b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelS5 b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelS5 b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelS5 b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelS5, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelS5, extractModelWith, List.any_eq_true] at hsat
        obtain ⟨sf, hsf_mem, hcond⟩ := hsat
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
        have hsign_eq : sf.sign = .pos := eq_of_beq hsign
        have hform_eq : sf.formula = .atom p := eq_of_beq hform
        have hlab_eq : sf.label = w := eq_of_beq hlab
        have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
          convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
        exact openBranch_noContradiction b hHopen (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hHopen w), ?_⟩
      intro _ hsat
      exact hsat
    | imp a c =>
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hHrule ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at hcond
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        have hpath : Relation.EqvGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelS5_r b acc ▸ hr
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hw' : w' ∈ modalKnownWorlds b :=
          (eqvGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikkaS5_box_pos b acc hH ψ w w' hmem hw')
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneS5 b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelS5_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneS5 b acc hH ψ w hmem
        exact ⟨w', extractModelS5_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.EqvGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelS5_r b acc ▸ hw'
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hw' : w' ∈ modalKnownWorlds b :=
          (eqvGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikkaS5_diamond_neg b acc hH ψ w w' hmem hw') hsψ

/-- **Top-loop propagation of `accSourcesKnown`, at `modalApplyOneS5`**: an open
`modalExpandBranchesS5` run started from `accSourcesKnown`-respecting branches returns an
`accSourcesKnown`-respecting branch.

This is a direct instantiation of the generic
`modalExpandBranchesGen_openBranch_accSourcesKnown` at `apply := modalApplyOneS5`, made possible
by that lemma's hypothesis having been *generalized* from the bundled
`spec : RuleApplicationSpec apply` to the raw `freshLocal` dichotomy it actually consumed. The
bundled form was unusable for S5 on principle -- `RuleApplicationSpec modalApplyOneS5` is
mathematically false at `rankStep` (`modalApplyOneS5_rankStep_not_dischargeable`) -- but the
`freshLocal` fact itself holds of `modalApplyOneS5` unconditionally
(`modalApplyOneS5_fresh_local`, task 515 Phase 7), since the S5 arms never touch accessibility.
Generalizing cost B nothing: its call site now passes `modalApplyOneB_spec.freshLocal`. -/
theorem modalExpandBranchesS5_openBranch_accSourcesKnown (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ p ∈ branches.zip accs, accSourcesKnown p.1 p.2) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen modalApplyOneS5 branches expandedSets accs fuel =
          .openBranch bR aR →
        accSourcesKnown bR aR :=
  modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneS5 modalApplyOneS5_fresh_local
    fuel

/-! ### How the four completeness ingredients are now supplied (historical scope note, RESOLVED)

This note tracked the four things `modalTableauS5_complete` (below) needs at the open branch
`(b, a)` returned by `modalTableauS5 φ0`. All four are now landed, after `modalTableauS5` was
re-based onto the witness-reuse rule `modalApplyOneS5w` (`S5Simplification.lean`), which
terminates at K's own `modalFuel`:

1. `F(φ0)@0 ∈ b` -- `modalExpandBranchesGen_openBranch_initial_mem` (fully generic).
2. `accSourcesKnown b a` -- `modalExpandBranchesGen_openBranch_accSourcesKnown` at
   `modalApplyOneS5w` (its only hypothesis is `modalApplyOneS5w_fresh_local`).
3. `accTargetsKnown b a` -- `modalExpandBranchesGen_openBranch_accTargetsKnown` (`BDriver.lean`),
   the top-loop propagation of the generic step-level fact, at `modalApplyOneS5w`.
4. `modalHintikkaSetGen modalApplyOneS5w b a` -- once "the wall", now supplied by
   `modalExpandBranchesHintikka` (`CompletenessLoop.lean`) at `Aux := ModalLoopAuxS5w φ0`. That
   parametric lift reaches the a-priori world bound through an opaque `Aux`, and S5w's
   instantiation discharges it by tag-cardinality counting (`S5wTagInv`/`S5wWorldInv`,
   `modalMaxWorld_lt_worldBound_of_S5w`) with **no rank map** -- superseding the abandoned route
   through a keyed loop invariant, which is retired to
   `specs/515_.../archive/04_s5loopinv-preservation.lean`. `hintikka_congr`
   (`S5Simplification.lean`) then converts this into the `modalHintikkaSetGen modalApplyOneS5`
   witness `modalOpenBranchS5_countermodel` consumes.

Note that fuel insufficiency is a *completeness*-only hazard, never a soundness one:
`modalExpandBranchesGen` at `fuel = 0` returns `.openBranch` whenever any branch is open
(`Saturation.lean`), never a premature `.closed`. This is why `modalTableauS5_sound` held
unconditionally at K's fuel even while the surface still ran the non-terminating rule. -/

/-- An open S5 Hintikka branch with `F(φ)@0 ∈ b` (and the known-world edge closure
`accSourcesKnown`/`accTargetsKnown`) yields an **equivalence-frame** Kripke countermodel to `φ`.
Mirrors `modalOpenBranchT_countermodel`/`modalOpenBranchB_countermodel`.

Together with `extractModelS5_equiv` (which discharges `s5FC` for free), this is the countermodel
half of S5 completeness: it is exactly the input `modalTableauS5_complete` would consume, and it
is available *now*, independent of the still-unbuilt spec-free Hintikka lift that would supply
the `modalHintikkaSetGen modalApplyOneS5 b acc` witness from an open tableau run. -/
theorem modalOpenBranchS5_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hH : modalHintikkaSetGen modalApplyOneS5 b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelS5 b acc) 0 φ :=
  (modalTruthLemmaS5 b acc hSrc hTgt hH φ 0).2 hF

/-! ## S5 Completeness and `s5Valid` Decidability

`modalTableauS5` now runs the witness-reuse rule `modalApplyOneS5w` (`S5Simplification.lean`),
which terminates at K's own `modalFuel`. That closes the four-item gap the scope note above
recorded: items 1-3 are supplied by the generic top-loop lemmas at `modalApplyOneS5w`
(`modalApplyOneS5w_fresh_local` is the only hypothesis they take), and item 4 -- "the wall" -- is
supplied by `modalExpandBranchesHintikka` (`CompletenessLoop.lean`) at
`Aux := ModalLoopAuxS5w φ₀`, whose world bound comes from tag-cardinality counting rather than a
rank map. `hintikka_congr` then converts the resulting `modalHintikkaSetGen modalApplyOneS5w`
witness into the `modalHintikkaSetGen modalApplyOneS5` witness `modalOpenBranchS5_countermodel`
consumes, so the entire landed countermodel half above is reused verbatim. -/

/-- **S5-completeness of the modal tableau**: if `φ₀` is `s5Valid`, the S5 tableau closes on it.
Contrapositively: an open branch is a genuine equivalence-frame countermodel.

Assembled from four landed pieces at `apply := modalApplyOneS5w` --
`modalExpandBranchesHintikka` (the spec-free Hintikka lift, at `ModalLoopAuxS5w`),
`modalExpandBranchesGen_openBranch_accSourcesKnown`/`_accTargetsKnown` (`BDriver.lean`),
`modalExpandBranchesGen_openBranch_initial_mem`, and `modalOpenBranchS5_countermodel` above --
with `hintikka_congr` (`S5Simplification.lean`) bridging the two rules' Hintikka sets and
`extractModelS5_equiv` discharging `s5FC` for free. Mirrors `modalTableauB_complete`. -/
theorem modalTableauS5_complete (φ₀ : Proposition Atom) (h : s5Valid φ₀) :
    modalTableauS5 φ₀ = .closed := by
  cases htab : modalTableauS5 φ₀ with
  | closed => rfl
  | openBranch b a =>
    exfalso
    have h' : modalExpandBranchesGen modalApplyOneS5w
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] (modalFuel φ₀) = .openBranch b a := htab
    have hH5w : modalHintikkaSetGen modalApplyOneS5w b a :=
      modalExpandBranchesHintikka modalApplyOneS5w modalApplyOneS5w_specCore φ₀
        (ModalLoopAuxS5w φ₀) (ModalLoopAuxS5w_stepPreserved φ₀) (ModalLoopAuxS5w_bounds φ₀)
        (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl (modalExpMeasure_entry_le_fuel φ₀)
        (by
          intro i bi ei ai hib hie hia
          match i with
          | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
            subst hib; subst hie; subst hia
            exact modalLoopInvHintikkaS5w_initial φ₀
          | n + 1 => simp at hib)
        b a h'
    have hH : modalHintikkaSetGen modalApplyOneS5 b a := (hintikka_congr b a).mp hH5w
    have hSrc : accSourcesKnown b a :=
      modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneS5w
        modalApplyOneS5w_fresh_local (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          exact accSourcesKnown_empty _)
        b a h'
    have hTgt : accTargetsKnown b a :=
      modalExpandBranchesGen_openBranch_accTargetsKnown modalApplyOneS5w
        modalApplyOneS5w_fresh_local (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          intro w w' hedge
          simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
          exact absurd hedge (by decide))
        b a h'
    have hmemInit : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
      modalExpandBranchesGen_openBranch_initial_mem modalApplyOneS5w (modalFuel φ₀)
        (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (fun b₀ hb₀ => by
          simp only [List.mem_singleton] at hb₀
          subst hb₀
          simp)
        b a h'
    have hFC : s5FC (extractModelS5 b a).r :=
      ⟨⟨extractModelS5_refl b a⟩, extractModelS5_rightEuclidean b a⟩
    exact modalOpenBranchS5_countermodel b a φ₀ hSrc hTgt hH hmemInit
      (h WorldIndex (extractModelS5 b a) hFC 0)

/-- **The modal S5 tableau decides S5-validity**: `modalTableauS5 φ₀` closes exactly when `φ₀` is
`s5Valid`. Combines soundness (`modalTableauS5_sound`, `FrameSoundness.lean`) with completeness
(above). Mirrors `tValid_decides`. -/
theorem s5Valid_decides (φ₀ : Proposition Atom) :
    modalTableauS5 φ₀ = .closed ↔ s5Valid φ₀ :=
  ⟨modalTableauS5_sound φ₀, modalTableauS5_complete φ₀⟩

/-- **S5-validity is decidable**: decide by running the modal S5 tableau and consulting
`s5Valid_decides`. No `Fintype Atom` assumption is needed, since the tableau computation itself
is the decision procedure. Mirrors `instDecidableTValid`.

This is the constructive witness to S5's decidability ([Blackburn-de Rijke-Venema][Blackburn2001],
§6.6 p.382, which also records S5's NP-completeness); the terminating witness-reuse rule
`modalApplyOneS5w` supplies the finite-search half. -/
instance instDecidableS5Valid (φ₀ : Proposition Atom) : Decidable (s5Valid φ₀) :=
  match h : modalTableauS5 φ₀ with
  | .closed => .isTrue ((s5Valid_decides φ₀).mp h)
  | .openBranch _ _ => .isFalse (fun hv => by rw [modalTableauS5_complete φ₀ hv] at h; cases h)

/-! ## 5 (Euclidean Frame) Extraction (task 515 Phase 20)

`extractModelS5_rightEuclidean` above already delivers *some* Euclidean coverage, but only for the
S5 route's `EqvGen`-closed model, which is unconditionally reflexive -- strictly narrower than a
genuine (non-reflexive) rooted Euclidean frame. This section instantiates Strategy B's
closure-at-extraction skeleton (`extractModelWith`) with `Relation.EuclGen`, the bespoke
right-Euclidean least-closure operator (`Cslib/Foundations/Relation/Euclidean.lean`), giving the
model relation genuine Euclidean-but-not-necessarily-reflexive structure. `extractModelS5*` and
`modalTruthLemmaS5` above are **untouched** -- this is a new, independent extraction, not a
modification of the S5 route. -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*right-Euclidean closure* `Relation.EuclGen` of `acc.hasEdge` as the model's relation (Strategy B,
closure-at-extraction, instantiated with `Cl := Relation.EuclGen`). Mirrors `extractModelS5`,
substituting `Relation.EuclGen` for `Relation.EqvGen` -- the one-word change the Euclidean route
was built for. -/
def extractModelFive
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (Relation.EuclGen) b acc

omit [Hashable Atom] in
/-- `extractModelFive`'s relation is exactly the right-Euclidean closure of `acc.hasEdge`. -/
lemma extractModelFive_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelFive b acc).r = Relation.EuclGen (fun w w' => acc.hasEdge w w' = true) := rfl

omit [Hashable Atom] in
/-- `extractModelFive`'s relation satisfies `Relation.RightEuclidean` unconditionally: immediate
from the generic instance `RightEuclidean (EuclGen r)` (`Euclidean.lean:147`). Discharges the
`fiveFC` witness (`FrameSoundness.lean`) for the Five countermodel. -/
lemma extractModelFive_rightEuclidean (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Relation.RightEuclidean (extractModelFive b acc).r := by
  rw [extractModelFive_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelFive`'s
(right-Euclidean-closure) relation via `Relation.EuclGen.base`. Needed to reuse the K bridge
lemmas (`hintikka_box_neg_gen`, `hintikka_diamond_pos_gen`), stated in terms of `acc.hasEdge`,
against `extractModelFive`'s closed relation. Mirrors `extractModelS5_hasEdge_imp_r`. -/
lemma extractModelFive_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelFive b acc).r w w' := by
  rw [extractModelFive_r]
  exact Relation.EuclGen.base h

/-! ### Raw Edge Root-Isolation and the Euclidean Closure's Root Behaviour

`modalFiveBoxAll`/`modalFiveDiaNegAll` (`FiveSimplification.lean`) structurally never place
propagated content at world `0`: a rooted (non-necessarily-reflexive) Euclidean frame need not
relate the root to itself, so universal propagation is unsound as a target there. This means the
Euclidean truth lemma's universal-propagation direction genuinely needs the tableau's accessibility
edges to never *target* the root -- true of every edge a real `modalTableauFive` run ever records
(mint arms always target a strictly fresh, hence positive, world; Route (a)'s reuse arm only ever
reuses a non-root witness, `modalApplyOneFive_agree_or_reuse_ne_root`, Phase 19b) -- but, exactly
like `accSourcesKnown`/`accTargetsKnown`, this phase takes it as an **abstract hypothesis** of the
truth lemma rather than re-deriving the top-loop preservation argument that would discharge it for
an actual tableau run. That discharge (alongside the existing `accSourcesKnown`/`accTargetsKnown`
witnesses) is Phase 21's obligation when it instantiates `modalTableauFive_complete` from a genuine
open branch.

This hypothesis is **not** a mere convenience: without it, the universal-propagation direction is
false in general. A raw edge `acc.hasEdge w 0` would witness a model relation `r w 0` that
`modalFiveBoxAll`'s root exclusion can never certify a matching branch formula `T(ψ)@0` for, so
`T(□ψ)@w ∈ b` would not entail `Satisfies M w (□ψ)`. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Raw edge root-isolation**: every recorded accessibility edge's *target* is a non-root world.
See the section note above for why this is a genuinely new, necessary hypothesis (not derivable
from `accSourcesKnown`/`accTargetsKnown` alone) and why discharging it for a real tableau run is
deferred to Phase 21. -/
def accTargetsNeRoot (acc : Accessibility) : Prop :=
  ∀ w w', acc.hasEdge w w' → w' ≠ (0 : WorldIndex)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every target reachable via the right-Euclidean closure of a root-isolated raw relation is
itself non-root: the `eucl` constructor's conclusion `EuclGen r b c` inherits its target `c`
directly from the second premise's own target, so induction reduces immediately to the raw
`accTargetsNeRoot` hypothesis at the `base` case and to the inner induction hypothesis (no use of
the first premise at all) at the `eucl` case. -/
lemma euclGen_ne_root_of_hasEdge_ne_root {acc : Accessibility} (hRoot : accTargetsNeRoot acc)
    {w w' : WorldIndex}
    (h : Relation.EuclGen (fun a c => acc.hasEdge a c = true) w w') :
    w' ≠ (0 : WorldIndex) := by
  induction h with
  | base hab => exact hRoot _ _ hab
  | eucl _ _ _ ihac => exact ihac

omit [DecidableEq Atom] [Hashable Atom] in
/-- **The root, as a *source* of the Euclidean closure, can only reach a target via a genuine
direct edge.** This is the fact `modalFiveBoxAll`'s root-trigger arm (Route (1)) is built to
match: `EuclGen r 0 w'` cannot arise from the `eucl` constructor, since that would require a
sub-derivation `EuclGen r a 0` reaching *target* `0` -- impossible by
`euclGen_ne_root_of_hasEdge_ne_root`. Hence the only remaining constructor, `base`, applies. -/
lemma euclGen_root_imp_hasEdge {acc : Accessibility} (hRoot : accTargetsNeRoot acc)
    {w' : WorldIndex}
    (h : Relation.EuclGen (fun a c => acc.hasEdge a c = true) (0 : WorldIndex) w') :
    acc.hasEdge 0 w' = true := by
  cases h with
  | base hab => exact hab
  | eucl hab _ => exact absurd rfl (euclGen_ne_root_of_hasEdge_ne_root hRoot hab)

omit [DecidableEq Atom] [Hashable Atom] in
/-- The right-Euclidean closure of `acc.hasEdge` never leaves `b`'s known-world set, in **both**
directions. Five analogue of `eqvGen_mem_modalKnownWorlds_iff`: `EuclGen`'s two constructors
(`base`/`eucl`) replace `EqvGen`'s four (`rel`/`refl`/`symm`/`trans`), but the argument is the
same shape -- the `base` case spends `accSourcesKnown`/`accTargetsKnown` on the one raw edge, and
the `eucl` case chains two `Iff`s sharing a common anchor (the shared first argument `a` of
`EuclGen r a b`/`EuclGen r a c`) via `Iff.symm`/`Iff.trans` instead of an explicit `trans` case. -/
lemma euclGen_mem_modalKnownWorlds_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    {w w' : WorldIndex}
    (h : Relation.EuclGen (fun a c => acc.hasEdge a c = true) w w') :
    w ∈ modalKnownWorlds b ↔ w' ∈ modalKnownWorlds b := by
  induction h with
  | base hab => exact iff_of_true (hSrc _ _ hab) (hTgt _ _ hab)
  | eucl _ _ ihab ihac => exact ihab.symm.trans ihac

/-! ## Five Modal Truth Lemma (task 515 Phase 20)

`modalFiveBoxAll`/`modalFiveDiaNegAll` (`FiveSimplification.lean`) are **root/non-root
asymmetric**: a non-root trigger propagates to the full non-root cluster (sound via the codomain
equivalence `Relation.rooted_cluster_isEquiv`, exactly the S5 argument transplanted onto
`cod (extractModelFive b acc).r`), while a root trigger propagates only to genuine direct
successors (sound via `hasEdge` alone, no closure reasoning needed). The bridge lemmas below
(`hintikkaFive_box_pos`/`hintikkaFive_diamond_neg`) package this root/non-root dichotomy; the
truth lemma's box/diamond cases then select the matching arm via `euclGen_root_imp_hasEdge`
(root trigger) or plain known-world membership (non-root trigger, via
`euclGen_mem_modalKnownWorlds_iff`). Every other case (propositional, and the box-negative/
diamond-positive mint directions) is unchanged in shape from `modalTruthLemmaS5`. -/

/-- `modalApplyOneFive` agrees with K's `modalApplyOne` at every purely propositional shape
(`atom`/`bot`/`imp`/`and`/`or`): chains `modalApplyOneFive_eq_of_not_mint_shape` (Five's own mint
shapes, diamond-positive/box-negative, are excluded) with
`modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg` (Five's own propagation shapes, box-positive/
diamond-negative, are excluded). Two-step where `modalApplyOneS5_eq_of_not_boxPos_diaNeg` is one
step, since Five (unlike plain S5) stages its rule through the guarded witness-reuse layer. -/
lemma modalApplyOneFive_eq_of_prop_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h1 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ))
    (h2 : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ))
    (h3 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ))
    (h4 : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)) :
    modalApplyOneFive sf b acc = modalApplyOne sf b acc := by
  rw [modalApplyOneFive_eq_of_not_mint_shape sf b acc ⟨h3, h4⟩,
    modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg sf b acc ⟨h1, h2⟩]

/-- **Five-analogue of `hintikkaS5_box_pos`**, root/non-root split: on an
`modalApplyOneFive`-saturated branch, `T(□ψ)@w ∈ b` forces `T(ψ)@v ∈ b` at any known, non-root
world `v`, PROVIDED that whenever the trigger `w` is itself the root, `v` is additionally a
genuine direct root successor (`acc.hasEdge 0 v`) -- exactly the root/non-root dichotomy
`modalFiveBoxAll` itself enforces. The proof is a `by_contra` mirroring `hintikkaS5_box_pos`
exactly once `hall`'s membership is established (via `modalFiveBoxAll_mem_of_root`/
`_mem_of_ne_root`), substituting the two-step `modalApplyOneFive_boxPos_eq` +
`modalApplyOneFiveProp` unfolding for S5's direct `modalApplyOneS5` unfolding. -/
lemma hintikkaFive_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneFive b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hv : v ∈ modalKnownWorlds b) (hvne : v ≠ (0 : WorldIndex))
    (hedge : w = (0 : WorldIndex) → acc.hasEdge 0 v = true) :
    (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFiveBoxAll b acc ψ w := by
    by_cases hw0 : w = (0 : WorldIndex)
    · subst hw0
      exact modalFiveBoxAll_mem_of_root hv hvne (hedge rfl) hnotin
    · exact modalFiveBoxAll_mem_of_ne_root hw0 hv hvne hnotin
  have hcond := hH.2.1 (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  have hK := modalApplyOne_boxPos_eq
    (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  rw [modalApplyOneFive_boxPos_eq] at hcond
  unfold modalApplyOneFiveProp at hcond
  rcases hp : modalApplyOne
      (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond hK
  simp only at hcond hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond
    split_ifs at hcond with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond _ hall)
  · dsimp only at hcond
    by_cases hkf : (⟨.pos, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **Five-analogue of `hintikkaS5_diamond_neg`**, dual of `hintikkaFive_box_pos`: `F(◇ψ)@w ∈ b`
forces `F(ψ)@v ∈ b` at any known, non-root world `v`, subject to the same root/non-root
dichotomy, via `modalFiveDiaNegAll`. -/
lemma hintikkaFive_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen modalApplyOneFive b acc)
    (ψ : Proposition Atom) (w v : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hv : v ∈ modalKnownWorlds b) (hvne : v ≠ (0 : WorldIndex))
    (hedge : w = (0 : WorldIndex) → acc.hasEdge 0 v = true) :
    (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  by_contra hnotin
  have hall : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFiveDiaNegAll b acc ψ w := by
    by_cases hw0 : w = (0 : WorldIndex)
    · subst hw0
      exact modalFiveDiaNegAll_mem_of_root hv hvne (hedge rfl) hnotin
    · exact modalFiveDiaNegAll_mem_of_ne_root hw0 hv hvne hnotin
  have hcond := hH.2.1 (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) hmem
  simp only at hcond
  have hK := modalApplyOne_diamondNeg_eq
    (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl ψ rfl b acc
  rw [modalApplyOneFive_diaNeg_eq] at hcond
  unfold modalApplyOneFiveProp at hcond
  rcases hp : modalApplyOne
      (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      with ⟨kResult, kAcc⟩
  rw [hp] at hcond hK
  simp only at hcond hK
  rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
  · dsimp only at hcond
    split_ifs at hcond with hemp
    · rw [List.isEmpty_iff] at hemp
      rw [hemp] at hall
      simp at hall
    · exact hnotin (hcond _ hall)
  · dsimp only at hcond
    by_cases hkf : (⟨.neg, ψ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ out0
    · exact hnotin (hcond _ (List.mem_append_left _ hkf))
    · refine hnotin (hcond _ (List.mem_append_right out0 ?_))
      simp only [List.mem_filter]
      refine ⟨hall, ?_⟩
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      intro x hx heq
      exact hkf (heq ▸ hx)

/-- **The Five modal truth lemma** (task 515 Phase 20): on an `modalApplyOneFive`-saturated open
branch whose recorded edges stay inside the known-world set (`hSrc`/`hTgt`) and never target the
root (`hRoot`), branch membership and `extractModelFive`-satisfaction agree, at every world and
both signs.

Mirrors `modalTruthLemmaS5` structurally: the propositional cases reuse the apply-agnostic
consistency kit and K's `modalApplyOne_*` bridge lemmas verbatim, routed through
`modalApplyOneFive_eq_of_prop_shape`; the box-negative/diamond-positive (minting) cases reuse the
free generic projection bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` directly, since a
raw recorded edge survives into the right-Euclidean closure via `extractModelFive_hasEdge_imp_r`.

The box-positive/diamond-negative cases are where Five differs from S5: rather than a single
uniform closure argument, they split on whether the trigger `w` is the root -- a root trigger
reads its edge witness off `euclGen_root_imp_hasEdge` directly (no closure detour), while a
non-root trigger reads known-world membership off `euclGen_mem_modalKnownWorlds_iff` (the
non-root cluster case, structurally the S5 argument transplanted via
`Relation.rooted_cluster_isEquiv`) -- and then read off the payload from
`hintikkaFive_box_pos`/`hintikkaFive_diamond_neg`. -/
lemma modalTruthLemmaFive
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hRoot : accTargetsNeRoot acc)
    (hH : modalHintikkaSetGen modalApplyOneFive b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelFive b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelFive b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModelFive b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModelFive b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModelFive b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModelFive b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    have hHopen : isModalClosed b = false := hH.1
    have hHrule := hH.2.1
    cases φ with
    | atom p =>
      refine ⟨?_, ?_⟩
      · intro hmem
        simp only [Satisfies, extractModelFive, extractModelWith]
        exact List.any_eq_true.mpr ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩
      · intro hmem hsat
        simp only [Satisfies, extractModelFive, extractModelWith, List.any_eq_true] at hsat
        obtain ⟨sf, hsf_mem, hcond⟩ := hsat
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
        have hsign_eq : sf.sign = .pos := eq_of_beq hsign
        have hform_eq : sf.formula = .atom p := eq_of_beq hform
        have hlab_eq : sf.label = w := eq_of_beq hlab
        have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
          convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
        exact openBranch_noContradiction b hHopen (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hHopen w), ?_⟩
      intro _ hsat
      exact hsat
    | imp a c =>
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a .bot, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · intro hmem
          have hcond := hHrule ⟨.pos, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · intro hmem
          have hcond := hHrule ⟨.neg, .imp a c, w⟩ hmem
          simp only at hcond
          rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
            (by simp)] at hcond
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hHrule ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      constructor
      · intro hmem
        have hcond := hHrule ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hHrule ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only at hcond
        rw [modalApplyOneFive_eq_of_prop_shape _ b acc (by simp) (by simp) (by simp)
          (by simp)] at hcond
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        have hpath : Relation.EuclGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelFive_r b acc ▸ hr
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hw'ne : w' ≠ (0 : WorldIndex) := euclGen_ne_root_of_hasEdge_ne_root hRoot hpath
        have hw' : w' ∈ modalKnownWorlds b :=
          (euclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw
        have hT : (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          hintikkaFive_box_pos b acc hH ψ w w' hmem hw' hw'ne
            (fun hz => euclGen_root_imp_hasEdge hRoot (hz ▸ hpath))
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1 hT
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg_gen modalApplyOneFive b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF
          (hall w' (extractModelFive_hasEdge_imp_r b acc hw'))
    | diamond ψ =>
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos_gen modalApplyOneFive b acc hH ψ w hmem
        exact ⟨w', extractModelFive_hasEdge_imp_r b acc hw',
          (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        have hpath : Relation.EuclGen (fun a c => acc.hasEdge a c = true) w w' :=
          extractModelFive_r b acc ▸ hw'
        have hw : w ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hmem
        have hw'ne : w' ≠ (0 : WorldIndex) := euclGen_ne_root_of_hasEdge_ne_root hRoot hpath
        have hw'known : w' ∈ modalKnownWorlds b :=
          (euclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt hpath).mp hw
        have hF : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
          hintikkaFive_diamond_neg b acc hH ψ w w' hmem hw'known hw'ne
            (fun hz => euclGen_root_imp_hasEdge hRoot (hz ▸ hpath))
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2 hF hsψ

/-- An open Five Hintikka branch with `F(φ)@0 ∈ b` (and the known-world edge closure
`accSourcesKnown`/`accTargetsKnown`/`accTargetsNeRoot`) yields a **right-Euclidean-frame** Kripke
countermodel to `φ`. Mirrors `modalOpenBranchS5_countermodel`.

Together with `extractModelFive_rightEuclidean` (which discharges `fiveFC` for free), this is the
countermodel half of Five completeness: it is exactly the input `modalTableauFive_complete`
(Phase 21) would consume. -/
theorem modalOpenBranchFive_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (hRoot : accTargetsNeRoot acc)
    (hH : modalHintikkaSetGen modalApplyOneFive b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModelFive b acc) 0 φ :=
  (modalTruthLemmaFive b acc hSrc hTgt hRoot hH φ 0).2 hF

/-! ## Top-Loop Propagation of `accTargetsNeRoot` (task 515 Phase 21)

`modalOpenBranchFive_countermodel` takes `accTargetsNeRoot acc` as an abstract hypothesis
(Phase 20's design finding: the universal-propagation direction of the truth lemma is false in
general without it). This section discharges it for a **real** `modalTableauFive`/
`modalExpandBranchesFive` run, exactly as `modalExpandBranchesGen_openBranch_accSourcesKnown`/
`_accTargetsKnown` (`BDriver.lean`) already discharge `hSrc`/`hTgt`, so `modalTableauFive_complete`
below can supply all three ingredients at once.

Unlike `accSourcesKnown`/`accTargetsKnown` (which are preserved by *any* rule satisfying the
generic `hFreshLocal` dichotomy), root-isolation is a fact specific to `modalApplyOneFive`'s own
guard shape (`FiveSimplification.lean`): a genuine mint targets `modalNextWorld b`, always
positive since `WorldIndex := Nat`; a Route (a) reuse targets a witness that
`modalApplyOneFive_agree_or_reuse_ne_root` (Phase 19b) already certifies non-root. Also unlike
`accSourcesKnown`/`accTargetsKnown` individually, `accTargetsNeRoot`'s single-step preservation
needs `accTargetsKnown` as an ambient invariant (to invoke
`modalApplyOneFiveProp_knownWorlds_step`'s own `hknown` hypothesis) -- the same "necessary THIRD
hypothesis beyond the plan's literal signature" pattern `S5Simplification.lean`'s
`modalStepBranchS5w_preserves_worldInv` documents for `S5wWorldInv`. The top-loop lemma below
therefore re-derives `accTargetsKnown` and `accTargetsNeRoot` together, in one induction, rather
than assuming the former has already been established by a separate run. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `Soundness.lean`'s `private lemma hasEdge_addEdge_cases` (unavailable
across files): decompose membership of an edge in `acc.addEdge w w'`. -/
private lemma hasEdge_addEdge_cases_Five {acc : Accessibility} {w w' a a' : WorldIndex}
    (h : (acc.addEdge w w').hasEdge a a' = true) :
    (a = w ∧ a' = w') ∨ acc.hasEdge a a' = true := by
  simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hw, hw'⟩ | h
  · exact Or.inl ⟨hw.symm, hw'.symm⟩
  · exact Or.inr h

omit [DecidableEq Atom] [Hashable Atom] in
/-- A fresh world is never the root: `modalNextWorld b = modalMaxWorld b + 1 ≥ 1`
unconditionally, since `WorldIndex := Nat`. -/
private lemma modalNextWorld_ne_zero_Five
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalNextWorld b ≠ (0 : WorldIndex) :=
  Nat.succ_ne_zero (modalMaxWorld b)

/-- **`modalApplyOneFive`'s edge-target root-isolation, per call**: whenever a step of
`modalApplyOneFive` records a new accessibility edge, that edge's target is non-root. Combines
`modalApplyOneFive_agree_or_reuse_ne_root` (Phase 19b: a reuse edge's target is the witness
`sf'.label`, already known non-root there) with `modalApplyOneFiveProp_knownWorlds_step` (a
genuine mint edge's target is `modalNextWorld b`, non-root since `WorldIndex := Nat` gives
`modalNextWorld b = modalMaxWorld b + 1 ≥ 1` unconditionally). The per-call companion
`modalStepBranchFive_preserves_accTargetsNeRoot` below needs. -/
lemma modalApplyOneFive_edge_target_ne_root
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    (modalApplyOneFive sf b acc).snd = acc ∨
      ∃ w', (modalApplyOneFive sf b acc).snd = acc.addEdge sf.label w' ∧
        w' ≠ (0 : WorldIndex) := by
  rcases modalApplyOneFive_agree_or_reuse_ne_root sf b acc with heq | ⟨sf', -, -, hsf'ne, heq⟩
  · rw [heq]
    rcases modalApplyOneFiveProp_knownWorlds_step sf b acc hsfmem hknown with
      ⟨hsnd, -⟩ | ⟨hsnd, -⟩
    · exact Or.inl hsnd
    · exact Or.inr ⟨modalNextWorld b, hsnd, modalNextWorld_ne_zero_Five b⟩
  · rw [heq]
    exact Or.inr ⟨sf'.label, rfl, hsf'ne⟩

/-- **Single-step preservation of `accTargetsNeRoot` at `modalApplyOneFive`**, given
`accTargetsKnown` as an ambient invariant. Mirrors `FmpMeasure.lean`'s
`modalStepBranch_preserves_accTargetsKnown_gen`'s edge-decomposition shape, substituting
`modalApplyOneFive_edge_target_ne_root` for the generic `hFreshLocal` dichotomy. -/
theorem modalStepBranchFive_preserves_accTargetsNeRoot
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneFive b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) (hroot : accTargetsNeRoot acc) :
    accTargetsNeRoot newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hnewAcc : newAcc = (modalApplyOneFive sf b acc).snd := by
    rcases hfstc : (modalApplyOneFive sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp only [Option.some.injEq, Prod.mk.injEq] at hsf; exact hsf.2.2.symm
    · rw [hfstc] at hsf; simp at hsf
  rw [hnewAcc]
  rcases modalApplyOneFive_edge_target_ne_root sf b acc hsfmem hknown with
    hsame | ⟨w', hsnd, hw'ne⟩
  · rw [hsame]; exact hroot
  · rw [hsnd]
    intro w1 w1' hedge
    rcases hasEdge_addEdge_cases_Five hedge with ⟨-, rfl⟩ | hold
    · exact hw'ne
    · exact hroot _ _ hold

/-- **Joint single-step preservation of `accTargetsKnown` and `accTargetsNeRoot`** at
`modalApplyOneFive`: bundles `modalStepBranch_preserves_accTargetsKnown_gen` (generic, at
`modalApplyOneFive_fresh_local`) with `modalStepBranchFive_preserves_accTargetsNeRoot` above, so
the top-loop induction below can maintain both invariants together without assuming either has
already been separately established. -/
theorem modalStepBranchFive_preserves_accTargetsKnown_and_NeRoot
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen modalApplyOneFive b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) (hroot : accTargetsNeRoot acc) :
    (∀ b' ∈ newBs, accTargetsKnown b' newAcc) ∧ accTargetsNeRoot newAcc :=
  ⟨modalStepBranch_preserves_accTargetsKnown_gen modalApplyOneFive modalApplyOneFive_fresh_local
      b e acc newBs newExps newAcc hstep hknown,
    modalStepBranchFive_preserves_accTargetsNeRoot b e acc newBs newExps newAcc hstep hknown hroot⟩

/-- **Top-loop propagation of `accTargetsKnown` and `accTargetsNeRoot`, together, at
`modalApplyOneFive`**: instantiates the generic `modalExpandBranchesGen_openBranch_gen`
(`BDriver.lean`) at the conjoined predicate `P := fun b acc => accTargetsKnown b acc ∧
accTargetsNeRoot acc`. This is the new top-loop ingredient `modalTableauFive_complete` (below)
needs alongside `accSourcesKnown`'s own top-loop lemma
(`modalExpandBranchesS5_openBranch_accSourcesKnown`'s Five analogue, applied directly at
`modalApplyOneFive_fresh_local`) to supply all of `hSrc`/`hTgt`/`hRoot` from a single real open
branch. -/
theorem modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      (∀ p ∈ branches.zip accs, accTargetsKnown p.1 p.2 ∧ accTargetsNeRoot p.2) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesGen modalApplyOneFive branches expandedSets accs fuel =
          .openBranch bR aR →
        accTargetsKnown bR aR ∧ accTargetsNeRoot aR :=
  modalExpandBranchesGen_openBranch_gen modalApplyOneFive
    (fun b acc => accTargetsKnown b acc ∧ accTargetsNeRoot acc)
    (by
      intro b e acc newBs newExps newAcc hstep hp b' hb'
      have hboth := modalStepBranchFive_preserves_accTargetsKnown_and_NeRoot b e acc newBs newExps
        newAcc hstep hp.1 hp.2
      exact ⟨hboth.1 b' hb', hboth.2⟩)
    fuel

/-! ## `ModalLoopAuxFive`: the Hintikka Wall's `Aux` Instantiation (Phase 21b, recipe step 3)

Assembles `modalStepBranchFive_preserves_worldInv` (`FiveSimplification.lean`) into the
`AuxStepPreserved`/`AuxBounds` pair `modalExpandBranchesHintikka` (`CompletenessLoop.lean`) needs
to supply the fourth completeness ingredient -- the Hintikka "wall" -- for a real
`modalTableauFive` run. Mirrors `ModalLoopAuxS5w`/`ModalLoopAuxS5w_bounds`/
`ModalLoopAuxS5w_stepPreserved`/`modalLoopInvHintikkaS5w_initial` (`CompletenessLoop.lean`).
Unlike `ModalLoopAuxS5w` (which ignores its `e` argument entirely), `ModalLoopAuxFive` genuinely
depends on `e` through `FiveWorldInvE`'s `expandedRootTagsFive` bookkeeping -- see
`FiveSimplification.lean`'s module note above `modalStepBranchFive_preserves_worldInv` for why
the root-triggered mint case needs this refinement over the plain, `e`-independent
`FiveWorldInv`. -/

/-- **Five's instantiation of `Aux`**: the `modalUniverse`-closure conjunct (needed since
`AuxStepPreserved`'s signature does not thread `ModalLoopInvHintikka.bClosure` as an ambient
hypothesis the way it threads `accFreshInv`/`accTargetsKnown`) paired with the `e`-aware
world-bound invariant `FiveWorldInvE`. The trailing `Accessibility` argument is required by
`Aux`'s shared signature (`AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka` all expect
`List (SignedFormula …) → List (SignedFormula …) → Accessibility → Prop`) but genuinely unused
here, mirroring `ModalLoopAuxS5w`. -/
@[nolint unusedArguments]
def ModalLoopAuxFive (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (_acc : Accessibility) : Prop :=
  (∀ x ∈ b, x ∈ modalUniverse φ₀) ∧ FiveWorldInvE φ₀ b e

omit [Hashable Atom] in
/-- **`ModalLoopAuxFive` entails the world bound**: the pointwise `AuxBounds` obligation,
discharged by routing `FiveWorldInvE` back to the already-landed, `e`-independent `FiveWorldInv`
(`FiveWorldInvE_imp_FiveWorldInv`) and then `modalMaxWorld_lt_worldBound_of_FiveWorldInv`
(Phase 19a). -/
theorem ModalLoopAuxFive_bounds (φ₀ : Proposition Atom) :
    AuxBounds φ₀ (ModalLoopAuxFive φ₀) := by
  rintro b e acc ⟨-, hWE⟩
  exact modalMaxWorld_lt_worldBound_of_FiveWorldInv (FiveWorldInvE_imp_FiveWorldInv hWE)

/-- **`ModalLoopAuxFive` is step-preserved**: the `AuxStepPreserved` obligation, discharged
directly by the already-landed `modalStepBranchFive_preserves_worldInv`
(`FiveSimplification.lean`), which is exactly this statement's conclusion under the same
hypotheses (`hb`/`hWE` packaged as `Aux`, `hFresh`/`hKnown` the ambient bookkeeping facts). -/
theorem ModalLoopAuxFive_stepPreserved (φ₀ : Proposition Atom) :
    AuxStepPreserved modalApplyOneFive (ModalLoopAuxFive φ₀) := by
  rintro b e acc newBs newExps newAcc hstep hFresh hKnown ⟨hb, hWE⟩ p hp
  exact modalStepBranchFive_preserves_worldInv hb hWE hFresh hKnown hstep p hp

/-- **Five's initial-configuration rank-free loop invariant**: `ModalLoopInvHintikka` holds of
the starting worklist entry `([F(φ₀)@0], [], ∅)`. Mirrors `modalLoopInvHintikkaS5w_initial`: the
five expanded-set conjuncts are all vacuous over `e = []`, `accFresh`/`accKnown` hold of the
empty relation, and the `aux` field reduces to two one-line facts -- `modalUniverse` membership
(the sole branch formula is `(.neg, φ₀)@0`) and `FiveWorldInvE`, because
`modalMaxWorld [F(φ₀)@0] = 0`, which bounds any sum of cardinalities. -/
lemma modalLoopInvHintikkaFive_initial (φ₀ : Proposition Atom) :
    ModalLoopInvHintikka modalApplyOneFive φ₀ (ModalLoopAuxFive φ₀)
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
    exact hmemU
  · simp only [FiveWorldInvE, modalMaxWorld, List.foldl_cons, List.foldl_nil]
    exact Nat.zero_le _

/-! ## Five Completeness and `fiveValid` Decidability (Phase 21b, recipe step 4)

`modalTableauFive` runs the witness-reuse, root-aware rule `modalApplyOneFive`
(`FiveSimplification.lean`), which terminates at K's own `modalFuel`. Items 1-3 of the
completeness ingredients are supplied by the generic top-loop lemmas at `modalApplyOneFive`
(`modalApplyOneFive_fresh_local` is the only hypothesis they take) plus the bespoke
`accTargetsNeRoot` top-loop pair (Phase 21.1), and item 4 -- "the wall" -- is supplied by
`modalExpandBranchesHintikka` (`CompletenessLoop.lean`) at `Aux := ModalLoopAuxFive φ₀` (recipe
steps 1-3 above). Unlike the S5 chain, no `hintikka_congr`-style bridge is needed:
`modalTableauFive` already runs `modalApplyOneFive` directly (Phase 21's investigation finding,
`modalOpenBranchFive_countermodel` above already takes `modalHintikkaSetGen modalApplyOneFive`
as its witness). -/

/-- **Five-completeness of the modal tableau**: if `φ₀` is `fiveValid`, the Five tableau closes
on it. Contrapositively: an open branch is a genuine right-Euclidean-frame countermodel.

Assembled from the four landed pieces at `apply := modalApplyOneFive` --
`modalExpandBranchesHintikka` (the spec-free Hintikka lift, at `ModalLoopAuxFive`),
`modalExpandBranchesGen_openBranch_accSourcesKnown` (`BDriver.lean`),
`modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot` (Phase 21.1),
`modalExpandBranchesGen_openBranch_initial_mem`, and `modalOpenBranchFive_countermodel` above --
with `extractModelFive_rightEuclidean` discharging `fiveFC` for free. Mirrors
`modalTableauS5_complete`. -/
theorem modalTableauFive_complete (φ₀ : Proposition Atom) (h : fiveValid φ₀) :
    modalTableauFive φ₀ = .closed := by
  cases htab : modalTableauFive φ₀ with
  | closed => rfl
  | openBranch b a =>
    exfalso
    have h' : modalExpandBranchesGen modalApplyOneFive
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] (modalFuel φ₀) = .openBranch b a := htab
    have hH : modalHintikkaSetGen modalApplyOneFive b a :=
      modalExpandBranchesHintikka modalApplyOneFive modalApplyOneFive_specCore φ₀
        (ModalLoopAuxFive φ₀) (ModalLoopAuxFive_stepPreserved φ₀) (ModalLoopAuxFive_bounds φ₀)
        (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl (modalExpMeasure_entry_le_fuel φ₀)
        (by
          intro i bi ei ai hib hie hia
          match i with
          | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hib hie hia
            subst hib; subst hie; subst hia
            exact modalLoopInvHintikkaFive_initial φ₀
          | n + 1 => simp at hib)
        b a h'
    have hSrc : accSourcesKnown b a :=
      modalExpandBranchesGen_openBranch_accSourcesKnown modalApplyOneFive
        modalApplyOneFive_fresh_local (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          exact accSourcesKnown_empty _)
        b a h'
    have hTgtRoot : accTargetsKnown b a ∧ accTargetsNeRoot a :=
      modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot (modalFuel φ₀)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
          subst hp
          refine ⟨?_, ?_⟩
          · intro w w' hedge
            simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
            exact absurd hedge (by decide)
          · intro w w' hedge
            simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
            exact absurd hedge (by decide))
        b a h'
    have hmemInit : (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
      modalExpandBranchesGen_openBranch_initial_mem modalApplyOneFive (modalFuel φ₀)
        (⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)
        [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty]
        rfl rfl
        (fun b₀ hb₀ => by
          simp only [List.mem_singleton] at hb₀
          subst hb₀
          simp)
        b a h'
    have hFC : fiveFC (extractModelFive b a).r := extractModelFive_rightEuclidean b a
    exact modalOpenBranchFive_countermodel b a φ₀ hSrc hTgtRoot.1 hTgtRoot.2 hH hmemInit
      (h WorldIndex (extractModelFive b a) hFC 0)

/-- **The modal Five tableau decides Five-validity**: `modalTableauFive φ₀` closes exactly when
`φ₀` is `fiveValid`. Combines soundness (`modalTableauFive_sound`, `FrameSoundness.lean`) with
completeness (above). Mirrors `s5Valid_decides`. -/
theorem fiveValid_decides (φ₀ : Proposition Atom) :
    modalTableauFive φ₀ = .closed ↔ fiveValid φ₀ :=
  ⟨modalTableauFive_sound φ₀, modalTableauFive_complete φ₀⟩

/-- **Five-validity is decidable**: decide by running the modal Five tableau and consulting
`fiveValid_decides`. No `Fintype Atom` assumption is needed, since the tableau computation itself
is the decision procedure. Mirrors `instDecidableS5Valid`.

This is the constructive witness to the Euclidean logic K5's decidability -- the terminating
witness-reuse, root-aware rule `modalApplyOneFive` supplies the finite-search half. -/
instance instDecidableFiveValid (φ₀ : Proposition Atom) : Decidable (fiveValid φ₀) :=
  match h : modalTableauFive φ₀ with
  | .closed => .isTrue ((fiveValid_decides φ₀).mp h)
  | .openBranch _ _ => .isFalse (fun hv => by rw [modalTableauFive_complete φ₀ hv] at h; cases h)

/-! ## KB5 (Symmetric-Euclidean/PER Frame) Extraction -- SCOUTING (task 515 Phase 23)

Extract a Kripke model using the *symmetric right-Euclidean closure*
`Relation.EuclGen (Relation.SymmGen acc.hasEdge)` as the model's relation: right-Euclidean
unconditionally (the generic `RightEuclidean (EuclGen r)` instance, regardless of base) and
symmetric because its base `Relation.SymmGen acc.hasEdge` is symmetric
(`EuclGen.symm_of_symm`/its packaged `Std.Symm` instance, `Euclidean.lean`). This is the *least*
`kb5FC`-satisfying relation containing every raw edge, hence forced, not merely convenient: see
the phase note below the extraction lemmas for why no other choice is available. -/

/-- Extract a Kripke model from an open branch `b` and accessibility relation `acc`, using the
*symmetric right-Euclidean closure* of `acc.hasEdge` as the model's relation. -/
def extractModelKb5
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom :=
  extractModelWith (fun r => Relation.EuclGen (Relation.SymmGen r)) b acc

omit [Hashable Atom] in
/-- `extractModelKb5`'s relation is exactly the symmetric right-Euclidean closure of
`acc.hasEdge`. -/
lemma extractModelKb5_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    (extractModelKb5 b acc).r =
      Relation.EuclGen (Relation.SymmGen (fun w w' => acc.hasEdge w w' = true)) := rfl

omit [Hashable Atom] in
/-- `extractModelKb5`'s relation satisfies `Relation.RightEuclidean` unconditionally: immediate
from the generic instance `RightEuclidean (EuclGen r)` (`Euclidean.lean:147`), regardless of the
base relation. -/
lemma extractModelKb5_rightEuclidean (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Relation.RightEuclidean (extractModelKb5 b acc).r := by
  rw [extractModelKb5_r]
  infer_instance

omit [Hashable Atom] in
/-- `extractModelKb5`'s relation satisfies `Std.Symm`: its base `Relation.SymmGen acc.hasEdge` is
symmetric (Mathlib's own unnamed instance), so `EuclGen`'s symmetry-preservation instance
(`Euclidean.lean`) applies. Discharges the `Std.Symm` half of `kb5FC` for the KB5 countermodel. -/
lemma extractModelKb5_symm (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    Std.Symm (extractModelKb5 b acc).r := by
  rw [extractModelKb5_r]
  infer_instance

omit [Hashable Atom] in
/-- Every raw tableau edge `acc.hasEdge w w' = true` survives into `extractModelKb5`'s relation
via `Relation.SymmGen.of_rel` then `Relation.EuclGen.base`. -/
lemma extractModelKb5_hasEdge_imp_r (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) {w w' : WorldIndex} (h : acc.hasEdge w w' = true) :
    (extractModelKb5 b acc).r w w' := by
  rw [extractModelKb5_r]
  exact Relation.EuclGen.base (Relation.SymmGen.of_rel h)

/-! ### KB5 Reachability & Known-Worlds Infrastructure (task 525 Phase 1)

The symmetrized base means the closure's `base` case is now `Relation.SymmGen acc.hasEdge`
(either `acc.hasEdge a c` or `acc.hasEdge c a`) rather than a single raw direction, so both the
known-worlds bridge and any root-reach argument must spend both `accSourcesKnown` and
`accTargetsKnown` at the `base` case (Five's `euclGen_mem_modalKnownWorlds_iff` only ever needed
one direction at a time, matching the raw relation's single direction). -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- The symmetric right-Euclidean closure of `acc.hasEdge` never leaves `b`'s known-world set, in
**both** directions. KB5 analogue of `euclGen_mem_modalKnownWorlds_iff`: the `base` case now
case-splits on which side of the symmetrization the raw edge came from (spending `accSourcesKnown`
then `accTargetsKnown`, or the reverse), while the `eucl` case is identical in shape. -/
lemma symmEuclGen_mem_modalKnownWorlds_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    {w w' : WorldIndex}
    (h : Relation.EuclGen (Relation.SymmGen (fun a c => acc.hasEdge a c = true)) w w') :
    w ∈ modalKnownWorlds b ↔ w' ∈ modalKnownWorlds b := by
  induction h with
  | base hab =>
    rcases hab with hab | hab
    · exact iff_of_true (hSrc _ _ hab) (hTgt _ _ hab)
    · exact iff_of_true (hTgt _ _ hab) (hSrc _ _ hab)
  | eucl _ _ ihab ihac => exact ihab.symm.trans ihac

omit [Hashable Atom] in
/-- **Root-reach membership**: whenever the root `0` reaches `w'` via `extractModelKb5`'s
relation, `w'` is a known world of `b`. Immediate corollary of
`symmEuclGen_mem_modalKnownWorlds_iff` at the always-known root (`label_mem_modalKnownWorlds`
applied to the branch's own initial formula is not needed here -- the root is known whenever the
closure relates it to anything, since `modalKnownWorlds` is populated from every label mentioned
in `b`, and a `base`/`eucl` derivation witnesses at least one raw edge touching `0`). This is the
*positive* direction the KB5 truth lemma's root case consumes: unlike Five's
`euclGen_root_imp_hasEdge` (which restricts the root to its **direct** successors only), this
lemma places every closure-reachable `w'` in the full known non-root cluster **without** asserting
a direct recorded edge -- exactly matching `modalKb5BoxAllFull`'s unconditional non-root cluster
dump. -/
lemma extractModelKb5_root_reach_mem_modalKnownWorlds
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hSrc : accSourcesKnown b acc) (hTgt : accTargetsKnown b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    {w' : WorldIndex} (h : (extractModelKb5 b acc).r (0 : WorldIndex) w') :
    w' ∈ modalKnownWorlds b :=
  (symmEuclGen_mem_modalKnownWorlds_iff b acc hSrc hTgt (extractModelKb5_r b acc ▸ h)).mp h0

/-! ### SCOUT: does `extractModelKb5`'s root reach stay within direct successors?

`modalFiveBoxAll`'s root-trigger arm (reused verbatim as `modalApplyOneKb5 := modalApplyOneFive`,
Phase 22) only ever forces propagated content at **direct** `acc.hasEdge 0 w'` successors of the
root. The Five truth lemma's root case is airtight *because* `Relation.EuclGen`'s closure of the
**raw, non-symmetrized** relation providably never lets the root reach anything beyond a direct
successor (`euclGen_root_imp_hasEdge`, consuming `accTargetsNeRoot`). The scout lemma below checks
whether the same containment survives once the base relation is **symmetrized** first -- i.e.
whether `euclGen_root_imp_hasEdge`'s KB5 analogue is even a true statement, before spending effort
on the truth lemma that would need it. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- **Scout counterexample**: with only two raw edges `0 → a` (root's direct successor) and
`a → c` (a's own child, `c` not a direct root successor), `extractModelKb5`'s relation relates the
root to `c` anyway -- `EuclGen (SymmGen r) 0 c` -- via `eucl (SymmGen.of_rel_symm h1) (base h2)`
(chaining through the *symmetrized* reverse edge `a → 0`, which shares source `a` with the raw
`a → c` edge). This is not an artifact of this specific closure choice: `r a 0` (forced by
`Std.Symm` applied to the required raw-edge survival `r 0 a`) and `r a c` (forced by raw-edge
survival alone) together force `r 0 c` via `RightEuclidean` alone, in **any** relation that is
simultaneously `kb5FC`-satisfying and preserves every raw edge -- so this is not repairable by
choosing a different closure operator. See the phase note below for the completeness-side
consequence. -/
private lemma extractModelKb5_root_reach_scout {α : Type*} {r : α → α → Prop} {w0 x y : α}
    (h1 : r w0 x) (h2 : r x y) :
    Relation.EuclGen (Relation.SymmGen r) w0 y :=
  Relation.EuclGen.eucl (Relation.EuclGen.base (Relation.SymmGen.of_rel_symm h1))
    (Relation.EuclGen.base (Relation.SymmGen.of_rel h2))

/-! ## Phase 23 Blocker: `modalTableauKb5_complete` -- genuine root-reach obstruction

**Finding (before any further code was written, per the mandatory pre-code analysis)**: the scout
lemma above confirms that `extractModelKb5`'s relation relates the root `0` to *every* world
reachable via a raw-edge path from a direct root successor, not merely to the direct successors
themselves. This is **forced**, not a choice: `extractModelKb5`'s relation is the *least*
`kb5FC`-satisfying relation containing every raw edge (`Relation.EuclGen.least` applied to
`Relation.SymmGen`), and raw-edge survival (`extractModelKb5_hasEdge_imp_r`, required by every
extraction in this file to support the box-negative/diamond-positive "K-style" witness cases,
mirroring `extractModelFive_hasEdge_imp_r`) plus `Std.Symm` plus `Relation.RightEuclidean`
*jointly* force `(extractModelKb5 b acc).r 0 c` whenever a raw chain `0 → a → ⋯ → c` exists, for
**any** relation satisfying those three properties -- not only this specific closure.

This breaks the truth lemma's root box-positive case: `T(□ψ)@0 ∈ b` needs `T(ψ)@w' ∈ b` for every
`w'` with `(extractModelKb5 b acc).r 0 w'`, but `modalFiveBoxAll`'s root arm (the same rule Phase
22 reuses unmodified for `modalApplyOneKb5`, deliberately restricted to direct successors --
*that* restriction is exactly what Five's soundness needs, since Five's root is not itself
reflexive) only forces content at **direct** `acc.hasEdge 0 w'` successors. A raw chain
`0 → a → c` (`a` non-root, minting a fresh witness `c` because no reuse candidate exists yet --
a routine, reachable shape under Route (a)'s witness-reuse mint arms) is exactly the case where
`T(ψ)@c ∈ b` is not forced by the existing rule, yet `(extractModelKb5 b acc).r 0 c` holds.

**This is not "5/KB5 completeness is impossible."** K5/KB5 completeness via a rooted Euclidean
tableau is well known to be achievable (Blackburn–de Rijke–Venema §4.8-4.9); the obstruction is
narrower and structural: `modalApplyOneKb5 := modalApplyOneFive` (Phase 22's literal alias,
"factor, not clone") is a **root-restricted** rule, deliberately so for Five's soundness, and that
restriction is precisely what a genuine KB5 completeness proof cannot route around while reusing
the *same* rule. Reaching `modalTableauKb5_complete` requires a **KB5-specific** propagation rule
(root box/diamond triggers dumping to the *full* known non-root cluster, matching the non-root
arm's own unconditional propagation, since the model forces the root into the same equivalence
class as everyone it can reach) -- and, once root becomes reflexive whenever it has a successor
(`Relation.symm_rightEuclidean_root_refl`, `Euclidean.lean`), the rule would additionally need to
propagate root's own box content back onto world `0` itself. Such a rule is no longer definable as
an alias of `modalApplyOneFive`: it needs its own soundness proof (the *same* unrestricted
propagation would be **unsound** for the strictly larger `fiveFC` class, so "factor, not clone"
does not apply to this direction), and its own completeness argument built to match. This is
substantial, genuinely new tableau-rule design and proof work -- comparable in scope to
Phases 15-21's Five construction -- not a proof-engineering gap closable by a different closure
choice or a cleverer induction. Marked `[BLOCKED]` per the escalation protocol; **not** re-narrated
as an impossibility, and not attempted with a `sorry` or placeholder. -/

end Cslib.Logic.Modal.Tableau

end
